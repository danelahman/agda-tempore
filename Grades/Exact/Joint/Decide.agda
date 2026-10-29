------------------------------------------------------------------------
-- Whether a lower and an upper expression with iteration have a      --
-- common run, decided.                                               --
--                                                                    --
-- In a commensurable time domain the ends of the letters of the two  --
-- expressions and the running times lie on the grid of one unit, so  --
-- the zones the walk on zones meets (`Joint.Zoned`) are computed in  --
-- counts of the unit (`Joint.Scale`), and normalised they lie within --
-- the largest count. The walk is searched over the tables of the     --
-- words of the two expressions (`Regular.Words`): a state is a state --
-- of each table and a phase, the letter in progress with its zone; a --
-- move reads the letters the walk moves past. Finitely many states   --
-- occur, so a search of the states reachable from the start          --
-- (`Regular.Reach`) decides whether one has both tables accepting    --
-- and no piece in progress: exactly when some run is common. The     --
-- search passes over states where either table is in its sink, from  --
-- which it accepts nothing.                                          --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain; Dense)
import Grades.Traces.RunningTimes as RunningTimes
import Grades.Durations.Monus as Monus
import Grades.Exact.Grid as Grid

module Grades.Exact.Joint.Decide
  {D : Duration} (T : TimeDomain D)
  (Op : Set) (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′)
  (name : Fin n → Op) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes T Op)
  (dense : Dense T) (κ : Duration.Carrier D) (κ-pos : Monus._<ᴰ_ T (Duration.0ᴰ D) κ)
  (commensurable : Grid.Commensurable T) where

open import Data.Bool.Base using (Bool; true; false) renaming (T to IsTrue)
open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (zero; suc)
open import Data.Fin.Subset using (_∈_)
open import Data.Fin.Subset.Properties using (_∈?_)
open import Data.List.Base using (List; []; _∷_; _++_; map; allFin; concatMap; upTo; foldr; filter)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺; ∈-allFin)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product using (Σ; Σ-syntax; ∃; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function.Bundles using (_⇔_; mk⇔; Equivalence)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (map′; _×-dec_; isYes; toWitness; fromWitness)
open import Data.Vec.Base using (Vec; lookup; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)

open import Grades.Durations.Nat using (ℕᵀ)
open import Grades.Durations.Monus T
open import Grades.Durations.Intervals T renaming (_∣_ to _∣ᶜ_)
import Grades.Durations.Intervals ℕᵀ as N

open import Grades.Exact.Grid T using (Unit)
open import Grades.Exact.Base T Op n code code-injective using (Word; _≟ₒ_)
open import Grades.Exact.Expression T Op n code code-injective running
open import Grades.Exact.Letters T Op n code code-injective running
  using (Letter; op; st; Word′; ⟦_⟧ʷ)
open import Grades.Exact.Finite T Op n code code-injective name code-name running dense κ κ-pos
  using (words; strWords; opw; members)
open import Grades.Exact.Regular.Words T Op n code code-injective name code-name running dense κ κ-pos
open import Grades.Exact.Regular.Decide T Op n code code-injective name code-name running
  dense κ κ-pos commensurable using (endsᴸ; endsᵁ; rtLos; rtHis; ptʰ; module OnUnit)
open import Grades.Regular.Coding as C using (Rx; size; letterAt)
  renaming (code to codeRx; allLits to litsAt)
import Grades.Regular.Automaton as Automaton
import Grades.Regular.Expression as RE
import Grades.Regular.Reach
import Data.Bool.ListAction
open import Grades.Exact.Joint T Op n code code-injective running
open import Grades.Exact.Joint.Zone T
import Grades.Exact.Joint.Zone ℕᵀ as Z
open import Grades.Exact.Joint.Zoned T Op n code code-injective running dense κ κ-pos

open RunningTimes.RunningTimes running using (rt; rt-bounded)
open RunningTimes T Op using (Bounded) renaming (fin to bfin)
open Equivalence using (to; from)

private
  name-code : ∀ o → name (code o) ≡ o
  name-code o = code-injective (code-name (code o))

  rtHi∈ : ∀ o → ptʰ (hi (rt o)) ∈ˡ rtHis
  rtHi∈ o = subst (λ o′ → ptʰ (hi (rt o′)) ∈ˡ rtHis) (name-code o)
                  (∈-map⁺ (λ c → ptʰ (hi (rt (name c)))) (∈-allFin (code o)))

  rtLo∈ : ∀ o → pt (lo (rt o)) ∈ˡ rtLos
  rtLo∈ o = subst (λ o′ → pt (lo (rt o′)) ∈ˡ rtLos) (name-code o)
                  (∈-map⁺ (λ c → pt (lo (rt (name c)))) (∈-allFin (code o)))

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

  ++ˡ : ∀ {A : Set} {xs ys : List A} {P : A → Set} → (∀ {q} → q ∈ˡ xs ++ ys → P q) → ∀ {q} → q ∈ˡ xs → P q
  ++ˡ h m = h (∈-++⁺ˡ m)

  ++ʳ : ∀ {A : Set} {xs ys : List A} {P : A → Set} → (∀ {q} → q ∈ˡ xs ++ ys → P q) → ∀ {q} → q ∈ˡ ys → P q
  ++ʳ {xs = xs} h m = h (∈-++⁺ʳ xs m)

------------------------------------------------------------------------
-- A lower and an upper expression

module Search (L : Expr lower) (U : Expr upper) where

  xs : List Carrier
  xs = 0ᴰ ∷ endsᴸ L ++ endsᵁ U ++ rtLos ++ rtHis

  open OnUnit xs
  open import Grades.Exact.Joint.Scale T δ-pos
    using (scZ; sc-⊕; sc-∩; sc-⊖; sc-Inh; sc-raise; sc-⊔ᶜ; sc-⊓ᶜ; sc-⊓ʰ)

  -- the words of each expression, as a table over the occurrences of
  -- its letters

  rX : Rx (Letter Cut)
  rX = toRx L

  rY : Rx (Letter Hi)
  rY = toRx U

  kX kY : ℕ
  kX = size rX
  kY = size rY

  lX : Fin kX → Letter Cut
  lX = letterAt rX

  lY : Fin kY → Letter Hi
  lY = letterAt rY

  module EX = RE kX
  module EY = RE kY
  module AX = Automaton kX
  module AY = Automaton kY

  X : AX.DFA
  X = EX.elab (codeRx rX)

  Y : AY.DFA
  Y = EY.elab (codeRx rY)

  ----------------------------------------------------------------------
  -- The ends on the grid

  private
    in-xs : ∀ {q} → q ∈ˡ endsᴸ L ++ endsᵁ U ++ rtLos ++ rtHis → OnGrid q
    in-xs m = listed (there m)

    on-0 : OnGrid 0ᴰ
    on-0 = listed (here refl)

    on-L : ∀ {q} → q ∈ˡ endsᴸ L → OnGrid q
    on-L m = in-xs (∈-++⁺ˡ m)

    on-U : ∀ {q} → q ∈ˡ endsᵁ U → OnGrid q
    on-U m = in-xs (∈-++⁺ʳ (endsᴸ L) (∈-++⁺ˡ m))

  on-lo : ∀ o → OnGrid (pt (lo (rt o)))
  on-lo o = in-xs (∈-++⁺ʳ (endsᴸ L) (∈-++⁺ʳ (endsᵁ U) (∈-++⁺ˡ (rtLo∈ o))))

  on-hi : ∀ o → OnGridʰ (hi (rt o))
  on-hi o with hi (rt o) | rtHi∈ o
  ... | fin c | m = in-xs (∈-++⁺ʳ (endsᴸ L) (∈-++⁺ʳ (endsᵁ U) (∈-++⁺ʳ rtLos m)))
  ... | ∞     | _ = tt

  private
    leavesᴸ : ∀ e → (∀ {q} → q ∈ˡ endsᴸ e → OnGrid q) → Leaves OnGridLᴸ e
    leavesᴸ ε _ = [] ∷ []
    leavesᴸ (ops A) _ = allOps (λ _ → tt) (members A)
    leavesᴸ (str S c) g =
      All.map (All.map (λ { (inj₁ refl) → g (here refl) ; (inj₂ refl) → on-0 })) (strAllᴸ S c)
    leavesᴸ (e ∣ f) g = leavesᴸ e (++ˡ g) , leavesᴸ f (++ʳ {xs = endsᴸ e} g)
    leavesᴸ (e · f) g = leavesᴸ e (++ˡ g) , leavesᴸ f (++ʳ {xs = endsᴸ e} g)
    leavesᴸ (e *) g = leavesᴸ e g

    leavesᵁ : ∀ e → (∀ {q} → q ∈ˡ endsᵁ e → OnGrid q) → Leaves OnGridL e
    leavesᵁ ε _ = [] ∷ []
    leavesᵁ (ops A) _ = allOps (λ _ → tt) (members A)
    leavesᵁ (str S ∞) _ = All.map (All.map (λ { refl → tt })) (strAllᵁ S ∞)
    leavesᵁ (str S (fin c)) g = All.map (All.map (λ { refl → g (here refl) })) (strAllᵁ S (fin c))
    leavesᵁ (e ∣ f) g = leavesᵁ e (++ˡ g) , leavesᵁ f (++ʳ {xs = endsᵁ e} g)
    leavesᵁ (e · f) g = leavesᵁ e (++ˡ g) , leavesᵁ f (++ʳ {xs = endsᵁ e} g)
    leavesᵁ (e *) g = leavesᵁ e g

  gX : ∀ a → OnGridLᴸ (lX a)
  gX = litsAt rX (allLits L (leavesᴸ L on-L))

  gY : ∀ b → OnGridL (lY b)
  gY = litsAt rY (allLits U (leavesᵁ U on-U))

  ----------------------------------------------------------------------
  -- The lengths the letters admit, and normalisation, in counts

  rtᴺ : Op → Z.Zone
  rtᴺ o = Z.⟨ downᶜ (lo (rt o)) , downʰ (hi (rt o)) ⟩ᶻ

  sc-rt : ∀ o → scZ (rtᴺ o) ≡ ⟨ lo (rt o) , hi (rt o) ⟩ᶻ
  sc-rt o = cong₂ ⟨_,_⟩ᶻ (sc-downᶜ (lo (rt o)) (on-lo o)) (sc-downʰ (hi (rt o)) (on-hi o))

  Aᴸᴺ : Fin kX → Z.Zone
  Aᴸᴺ a with lX a
  ... | op o   = rtᴺ o
  ... | st S c = Z.⟨ N.0⁺ N.⊔ᶜ downᶜ c , N.∞ ⟩ᶻ

  Aᵁᴺ : Fin kY → Z.Zone
  Aᵁᴺ b with lY b
  ... | op o   = rtᴺ o
  ... | st S h = Z.⟨ N.0⁺ , downʰ h ⟩ᶻ

  sc-Aᴸ : ∀ a → scZ (Aᴸᴺ a) ≡ Aᴸ (lX a)
  sc-Aᴸ a with lX a | gX a
  ... | op o   | _ = sc-rt o
  ... | st S c | g = cong (⟨_, ∞ ⟩ᶻ) (trans (sc-⊔ᶜ N.0⁺ (downᶜ c)) (cong (0⁺ ⊔ᶜ_) (sc-downᶜ c g)))

  sc-Aᵁ : ∀ b → scZ (Aᵁᴺ b) ≡ Aᵁ (lY b)
  sc-Aᵁ b with lY b | gY b
  ... | op o   | _ = sc-rt o
  ... | st S h | g = cong (⟨ 0⁺ ,_⟩ᶻ) (sc-downʰ h g)

  -- what normalising needs of a letter

  data NL : Set where
    nop : N.Hi → NL
    nst : N.Cut → NL

  data NU : Set where
    uop  : N.Hi → NU
    ufin : N.Cut → NU
    uinf : NU

  normL′ : NL → Z.Zone → Z.Zone
  normL′ (nop h) I = I Z.∩ᶻ Z.⟨ N.0⁻ , h ⟩ᶻ
  normL′ (nst c) I = Z.⟨ Z.loᶻ I N.⊓ᶜ c , Z.raise c (Z.hiᶻ I) ⟩ᶻ

  normU′ : NU → Z.Zone → Z.Zone
  normU′ (uop h)  I = I Z.∩ᶻ Z.⟨ N.0⁻ , h ⟩ᶻ
  normU′ (ufin c) I = I Z.∩ᶻ Z.⟨ N.0⁻ , N.fin c ⟩ᶻ
  normU′ uinf     I = Z.⟨ N.0⁺ , N.∞ ⟩ᶻ

  ndL₀ : Fin kX → NL
  ndL₀ a with lX a
  ... | op o   = nop (downʰ (hi (rt o)))
  ... | st S c = nst (downᶜ c)

  ndU₀ : Fin kY → NU
  ndU₀ b with lY b
  ... | op o         = uop (downʰ (hi (rt o)))
  ... | st S (fin c) = ufin (downᶜ c)
  ... | st S ∞       = uinf

  normᴸᴺ : Fin kX → Z.Zone → Z.Zone
  normᴸᴺ a = normL′ (ndL₀ a)

  normᵁᴺ : Fin kY → Z.Zone → Z.Zone
  normᵁᴺ b = normU′ (ndU₀ b)

  sc-normᴸ : ∀ a I → scZ (normᴸᴺ a I) ≡ normᴸ (lX a) (scZ I)
  sc-normᴸ a I with lX a | gX a
  ... | op o   | _ =
    trans (sc-∩ I Z.⟨ N.0⁻ , downʰ (hi (rt o)) ⟩ᶻ)
          (cong (λ h → scZ I ∩ᶻ ⟨ 0⁻ , h ⟩ᶻ) (sc-downʰ (hi (rt o)) (on-hi o)))
  ... | st S c | g =
    cong₂ ⟨_,_⟩ᶻ (trans (sc-⊓ᶜ (Z.loᶻ I) (downᶜ c)) (cong (scᶜ (Z.loᶻ I) ⊓ᶜ_) (sc-downᶜ c g)))
                 (trans (sc-raise (downᶜ c) (Z.hiᶻ I)) (cong (λ c′ → raise c′ (scʰ (Z.hiᶻ I))) (sc-downᶜ c g)))

  sc-normᵁ : ∀ b I → scZ (normᵁᴺ b I) ≡ normᵁ (lY b) (scZ I)
  sc-normᵁ b I with lY b | gY b
  ... | op o         | _ =
    trans (sc-∩ I Z.⟨ N.0⁻ , downʰ (hi (rt o)) ⟩ᶻ)
          (cong (λ h → scZ I ∩ᶻ ⟨ 0⁻ , h ⟩ᶻ) (sc-downʰ (hi (rt o)) (on-hi o)))
  ... | st S (fin c) | g =
    trans (sc-∩ I Z.⟨ N.0⁻ , N.fin (downᶜ c) ⟩ᶻ)
          (cong (λ c′ → scZ I ∩ᶻ ⟨ 0⁻ , fin c′ ⟩ᶻ) (sc-downᶜ c g))
  ... | st S ∞       | _ = refl

  ----------------------------------------------------------------------
  -- What the letters allow, decided in counts

  ZeroL : Letter Cut → Set
  ZeroL (op _)   = ⊥
  ZeroL (st S c) = _∈ᵉ_ 0ᴰ {lower} c

  ZeroU : Letter Hi → Set
  ZeroU (op _)   = ⊥
  ZeroU (st S h) = _∈ᵉ_ 0ᴰ {upper} h

  zeroL? : ∀ a → Dec (ZeroL (lX a))
  zeroL? a with lX a | gX a
  ... | op o   | _ = no λ ()
  ... | st S c | g =
    map′ (λ r → subst (_⊑ (0ᴰ ∣ᶜ ⁻)) (sc-downᶜ c g) (scᶜ-⊑ r))
         (λ r → scᶜ-⊑⁻ (subst (_⊑ (0ᴰ ∣ᶜ ⁻)) (sym (sc-downᶜ c g)) r))
         (downᶜ c N.⊑? (0 N.∣ N.⁻))

  zeroU? : ∀ b → Dec (ZeroU (lY b))
  zeroU? b with lY b | gY b
  ... | op o   | _ = no λ ()
  ... | st S h | g =
    map′ (λ r → subst (fin (0ᴰ ∣ᶜ ⁺) ⊑ʰ_) (sc-downʰ h g) (scʰ-⊑ {N.fin (0 N.∣ N.⁺)} r))
         (λ r → scʰ-⊑⁻ {N.fin (0 N.∣ N.⁺)} (subst (fin (0ᴰ ∣ᶜ ⁺) ⊑ʰ_) (sym (sc-downʰ h g)) r))
         (N.fin (0 N.∣ N.⁺) N.⊑ʰ? downʰ h)

  meets? : ∀ {A B : Set} (ℓ : Letter A) (m : Letter B) → Dec (Meets ℓ m)
  meets? (op o)   (op o′)  = no λ ()
  meets? (op o)   (st S _) = code o ∈? S
  meets? (st S _) (op o)   = code o ∈? S
  meets? (st _ _) (st _ _) = yes tt

  OpOp′ : Letter Cut → Letter Hi → Set
  OpOp′ ℓ m = Σ[ o ∈ Op ] ℓ ≡ op o × m ≡ op o

  opop?′ : ∀ ℓ m → Dec (OpOp′ ℓ m)
  opop?′ (op o)   (op o′)  with o ≟ₒ o′
  ... | yes refl = yes (o , refl , refl)
  ... | no ¬e    = no λ { (_ , refl , refl) → ¬e refl }
  opop?′ (op o)   (st _ _) = no λ { (_ , _ , ()) }
  opop?′ (st _ _) _        = no λ { (_ , () , _) }

  OpOp : Fin kX → Fin kY → Set
  OpOp a b = OpOp′ (lX a) (lY b)

  opop? : ∀ a b → Dec (OpOp a b)
  opop? a b = opop?′ (lX a) (lY b)

  ----------------------------------------------------------------------
  -- The search, over the two tables, taken as arguments so that each is
  -- computed once

  wfX : AX.WellFormed X
  wfX = EX.elab-wf (codeRx rX)

  wfY : AY.WellFormed Y
  wfY = EY.elab-wf (codeRx rY)

  -- what the moves read of the letters, tabulated, so that it is
  -- computed once per letter

  record Memo : Set where
    field
      vlX : Vec (Letter Cut) kX
      vlY : Vec (Letter Hi) kY
      vA  : Vec Z.Zone kX
      vB  : Vec Z.Zone kY
      vnL : Vec NL kX
      vnU : Vec NU kY
      vzL : Vec Bool kX
      vzU : Vec Bool kY

  memo : Memo
  memo = record
    { vlX = tabulate lX ; vlY = tabulate lY ; vA = tabulate Aᴸᴺ ; vB = tabulate Aᵁᴺ
    ; vnL = tabulate ndL₀ ; vnU = tabulate ndU₀
    ; vzL = tabulate (λ a → isYes (zeroL? a)) ; vzU = tabulate (λ b → isYes (zeroU? b)) }

  record Faithful (M : Memo) : Set where
    open Memo M
    field
      elX : ∀ a → lookup vlX a ≡ lX a
      elY : ∀ b → lookup vlY b ≡ lY b
      eA  : ∀ a → lookup vA a ≡ Aᴸᴺ a
      eB  : ∀ b → lookup vB b ≡ Aᵁᴺ b
      enL : ∀ a → lookup vnL a ≡ ndL₀ a
      enU : ∀ b → lookup vnU b ≡ ndU₀ b
      ezL : ∀ a → lookup vzL a ≡ isYes (zeroL? a)
      ezU : ∀ b → lookup vzU b ≡ isYes (zeroU? b)

  memo-faithful : Faithful memo
  memo-faithful = record
    { elX = lookup∘tabulate lX ; elY = lookup∘tabulate lY
    ; eA = lookup∘tabulate Aᴸᴺ ; eB = lookup∘tabulate Aᵁᴺ
    ; enL = lookup∘tabulate ndL₀ ; enU = lookup∘tabulate ndU₀
    ; ezL = lookup∘tabulate (λ a → isYes (zeroL? a)) ; ezU = lookup∘tabulate (λ b → isYes (zeroU? b)) }

  module Moves (X′ : AX.DFA) (Y′ : AY.DFA) (wfX′ : AX.WellFormed X′) (wfY′ : AY.WellFormed Y′)
               (M : Memo) (F : Faithful M) where

    ----------------------------------------------------------------------
    -- States and moves

    data Ph : Set where
      zs : Ph
      zl : Fin kX → Z.Zone → Ph
      zu : Fin kY → Z.Zone → Ph

    State : Set
    State = ℕ × ℕ × Ph

    ⟦_⟧ᴾ : Ph → ZPhase
    ⟦ zs     ⟧ᴾ = zsync
    ⟦ zl a I ⟧ᴾ = zinL (lX a) (scZ I)
    ⟦ zu b I ⟧ᴾ = zinU (lY b) (scZ I)

    data AtLᴾ : Ph → Set where
      zs : AtLᴾ zs
      zu : ∀ {b I} → AtLᴾ (zu b I)

    data AtUᴾ : Ph → Set where
      zs : AtUᴾ zs
      zl : ∀ {a I} → AtUᴾ (zl a I)

    nx : ℕ → Fin kX → ℕ
    nx = AX.next X′

    ny : ℕ → Fin kY → ℕ
    ny = AY.next Y′

    data Step : State → State → Set where
      skipLᴾ : ∀ {p q φ a} → AtLᴾ φ → ZeroL (lX a) → Step (p , q , φ) (nx p a , q , φ)
      skipUᴾ : ∀ {p q φ b} → AtUᴾ φ → ZeroU (lY b) → Step (p , q , φ) (p , ny q b , φ)
      opopᴾ  : ∀ {p q a b} → OpOp a b
             → Step (p , q , zs) (nx p a , ny q b , zs)
      syncLᴾ : ∀ {p q a b} → Meets (lX a) (lY b) → Z.Inh (Aᴸᴺ a) → Z.Inh (normᵁᴺ b (Aᴸᴺ a))
             → Step (p , q , zs) (nx p a , ny q b , zu b (normᵁᴺ b (Aᴸᴺ a)))
      syncUᴾ : ∀ {p q a b} → Meets (lX a) (lY b) → Z.Inh (Aᵁᴺ b) → Z.Inh (normᴸᴺ a (Aᵁᴺ b))
             → Step (p , q , zs) (nx p a , ny q b , zl a (normᴸᴺ a (Aᵁᴺ b)))
      syncBᴾ : ∀ {p q a b} → Meets (lX a) (lY b) → Z.Inh (Aᴸᴺ a Z.∩ᶻ Aᵁᴺ b)
             → Step (p , q , zs) (nx p a , ny q b , zs)
      firstLᴾ : ∀ {p q a b I} → Meets (lX a) (lY b) → Z.Inh (Aᴸᴺ a) → Z.Inh (normᵁᴺ b (I Z.⊕ᶻ Aᴸᴺ a))
              → Step (p , q , zu b I) (nx p a , q , zu b (normᵁᴺ b (I Z.⊕ᶻ Aᴸᴺ a)))
      lateUᴾ  : ∀ {p q a b I} → Meets (lX a) (lY b) → Z.Inh (Aᵁᴺ b) → Z.Inh (Aᵁᴺ b Z.⊖ᶻ I)
              → Z.Inh (normᴸᴺ a (Aᵁᴺ b Z.⊖ᶻ I))
              → Step (p , q , zu b I) (nx p a , q , zl a (normᴸᴺ a (Aᵁᴺ b Z.⊖ᶻ I)))
      bothUᴾ  : ∀ {p q a b I} → Meets (lX a) (lY b) → Z.Inh (Aᴸᴺ a) → Z.Inh ((I Z.⊕ᶻ Aᴸᴺ a) Z.∩ᶻ Aᵁᴺ b)
              → Step (p , q , zu b I) (nx p a , q , zs)
      firstUᴾ : ∀ {p q a b I} → Meets (lX a) (lY b) → Z.Inh (Aᵁᴺ b) → Z.Inh (normᴸᴺ a (I Z.⊕ᶻ Aᵁᴺ b))
              → Step (p , q , zl a I) (p , ny q b , zl a (normᴸᴺ a (I Z.⊕ᶻ Aᵁᴺ b)))
      lateLᴾ  : ∀ {p q a b I} → Meets (lX a) (lY b) → Z.Inh (Aᴸᴺ a) → Z.Inh (Aᴸᴺ a Z.⊖ᶻ I)
              → Z.Inh (normᵁᴺ b (Aᴸᴺ a Z.⊖ᶻ I))
              → Step (p , q , zl a I) (p , ny q b , zu b (normᵁᴺ b (Aᴸᴺ a Z.⊖ᶻ I)))
      bothLᴾ  : ∀ {p q a b I} → Meets (lX a) (lY b) → Z.Inh (Aᵁᴺ b) → Z.Inh ((I Z.⊕ᶻ Aᵁᴺ b) Z.∩ᶻ Aᴸᴺ a)
              → Step (p , q , zl a I) (p , ny q b , zs)

    ----------------------------------------------------------------------
    -- Paths of moves are walks on zones

    AccX : ℕ → List (Fin kX) → Set
    AccX p u = IsTrue (AX.isFinal X′ (AX.run X′ p u))

    AccY : ℕ → List (Fin kY) → Set
    AccY q u = IsTrue (AY.isFinal Y′ (AY.run Y′ q u))

    -- an accepting state reached by moves

    data Reach : State → Set where
      stop : ∀ {p q} → IsTrue (AX.isFinal X′ p) → IsTrue (AY.isFinal Y′ q) → Reach (p , q , zs)
      go   : ∀ {s s′} → Step s s′ → Reach s′ → Reach s

    private
      inh⇑ : ∀ {Zn Zt} → scZ Zn ≡ Zt → Z.Inh Zn → Inh Zt
      inh⇑ {Zn} e i = subst Inh e (to (sc-Inh Zn) i)

      inh⇓ : ∀ {Zn Zt} → scZ Zn ≡ Zt → Inh Zt → Z.Inh Zn
      inh⇓ {Zn} e i = from (sc-Inh Zn) (subst Inh (sym e) i)

      -- the zones of the moves, scaled

      e-sL : ∀ a b → scZ (normᵁᴺ b (Aᴸᴺ a)) ≡ normᵁ (lY b) (Aᴸ (lX a))
      e-sL a b = trans (sc-normᵁ b (Aᴸᴺ a)) (cong (normᵁ (lY b)) (sc-Aᴸ a))

      e-sU : ∀ a b → scZ (normᴸᴺ a (Aᵁᴺ b)) ≡ normᴸ (lX a) (Aᵁ (lY b))
      e-sU a b = trans (sc-normᴸ a (Aᵁᴺ b)) (cong (normᴸ (lX a)) (sc-Aᵁ b))

      e-sB : ∀ a b → scZ (Aᴸᴺ a Z.∩ᶻ Aᵁᴺ b) ≡ Aᴸ (lX a) ∩ᶻ Aᵁ (lY b)
      e-sB a b = trans (sc-∩ (Aᴸᴺ a) (Aᵁᴺ b)) (cong₂ _∩ᶻ_ (sc-Aᴸ a) (sc-Aᵁ b))

      e-fL : ∀ a b I → scZ (normᵁᴺ b (I Z.⊕ᶻ Aᴸᴺ a)) ≡ normᵁ (lY b) (scZ I ⊕ᶻ Aᴸ (lX a))
      e-fL a b I = trans (sc-normᵁ b _) (cong (normᵁ (lY b)) (trans (sc-⊕ I (Aᴸᴺ a)) (cong (scZ I ⊕ᶻ_) (sc-Aᴸ a))))

      e-lU : ∀ a b I → scZ (normᴸᴺ a (Aᵁᴺ b Z.⊖ᶻ I)) ≡ normᴸ (lX a) (Aᵁ (lY b) ⊖ᶻ scZ I)
      e-lU a b I = trans (sc-normᴸ a _) (cong (normᴸ (lX a)) (trans (sc-⊖ (Aᵁᴺ b) I) (cong (_⊖ᶻ scZ I) (sc-Aᵁ b))))

      e-bU : ∀ a b I → scZ ((I Z.⊕ᶻ Aᴸᴺ a) Z.∩ᶻ Aᵁᴺ b) ≡ (scZ I ⊕ᶻ Aᴸ (lX a)) ∩ᶻ Aᵁ (lY b)
      e-bU a b I = trans (sc-∩ (I Z.⊕ᶻ Aᴸᴺ a) (Aᵁᴺ b)) (cong₂ _∩ᶻ_ (trans (sc-⊕ I (Aᴸᴺ a)) (cong (scZ I ⊕ᶻ_) (sc-Aᴸ a))) (sc-Aᵁ b))

      e-fU : ∀ a b I → scZ (normᴸᴺ a (I Z.⊕ᶻ Aᵁᴺ b)) ≡ normᴸ (lX a) (scZ I ⊕ᶻ Aᵁ (lY b))
      e-fU a b I = trans (sc-normᴸ a _) (cong (normᴸ (lX a)) (trans (sc-⊕ I (Aᵁᴺ b)) (cong (scZ I ⊕ᶻ_) (sc-Aᵁ b))))

      e-lL : ∀ a b I → scZ (normᵁᴺ b (Aᴸᴺ a Z.⊖ᶻ I)) ≡ normᵁ (lY b) (Aᴸ (lX a) ⊖ᶻ scZ I)
      e-lL a b I = trans (sc-normᵁ b _) (cong (normᵁ (lY b)) (trans (sc-⊖ (Aᴸᴺ a) I) (cong (_⊖ᶻ scZ I) (sc-Aᴸ a))))

      e-bL : ∀ a b I → scZ ((I Z.⊕ᶻ Aᵁᴺ b) Z.∩ᶻ Aᴸᴺ a) ≡ (scZ I ⊕ᶻ Aᵁ (lY b)) ∩ᶻ Aᴸ (lX a)
      e-bL a b I = trans (sc-∩ (I Z.⊕ᶻ Aᵁᴺ b) (Aᴸᴺ a)) (cong₂ _∩ᶻ_ (trans (sc-⊕ I (Aᵁᴺ b)) (cong (scZ I ⊕ᶻ_) (sc-Aᵁ b))) (sc-Aᴸ a))

      -- passing a letter admitting no time

      zskipL′ : ∀ ℓ {v w φ} → ZeroL ℓ → ZAtL φ → ZWalk v w φ → ZWalk (ℓ ∷ v) w φ
      zskipL′ (op o)   () _ _
      zskipL′ (st S c) z  a j = zskipL a z j

      zskipU′ : ∀ m {v w φ} → ZeroU m → ZAtU φ → ZWalk v w φ → ZWalk v (m ∷ w) φ
      zskipU′ (op o)   () _ _
      zskipU′ (st S h) z  a j = zskipU a z j

      atL : ∀ {φ} → AtLᴾ φ → ZAtL ⟦ φ ⟧ᴾ
      atL zs = zsync
      atL zu = zinU

      atU : ∀ {φ} → AtUᴾ φ → ZAtU ⟦ φ ⟧ᴾ
      atU zs = zsync
      atU zl = zinL


    reach-sound : ∀ {p q φ} → Reach (p , q , φ)
                → Σ[ u ∈ List (Fin kX) ] Σ[ u′ ∈ List (Fin kY) ]
                    AccX p u × AccY q u′ × ZWalk (map lX u) (map lY u′) ⟦ φ ⟧ᴾ
    reach-sound (stop f g) = [] , [] , f , g , zdone
    reach-sound (go (skipLᴾ {a = a} at z) r) with reach-sound r
    ... | u , u′ , f , g , j = a ∷ u , u′ , f , g , zskipL′ (lX a) z (atL at) j
    reach-sound (go (skipUᴾ {b = b} at z) r) with reach-sound r
    ... | u , u′ , f , g , j = u , b ∷ u′ , f , g , zskipU′ (lY b) z (atU at) j
    reach-sound (go (opopᴾ {a = a} {b} (o , ea , eb)) r) with reach-sound r
    ... | u , u′ , f , g , j =
      a ∷ u , b ∷ u′ , f , g ,
      subst₂ (λ ℓ m → ZWalk (ℓ ∷ map lX u) (m ∷ map lY u′) zsync) (sym ea) (sym eb)
        (zopop (lo◁hi (rt o)) j)
    reach-sound (go (syncLᴾ {a = a} {b} mt i₁ i₂) r) with reach-sound r
    ... | u , u′ , f , g , j =
      a ∷ u , b ∷ u′ , f , g ,
      zsyncL mt (inh⇑ (sc-Aᴸ a) i₁) (inh⇑ (e-sL a b) i₂) (subst (λ Z → ZWalk _ _ (zinU (lY b) Z)) (e-sL a b) j)
    reach-sound (go (syncUᴾ {a = a} {b} mt i₁ i₂) r) with reach-sound r
    ... | u , u′ , f , g , j =
      a ∷ u , b ∷ u′ , f , g ,
      zsyncU mt (inh⇑ (sc-Aᵁ b) i₁) (inh⇑ (e-sU a b) i₂) (subst (λ Z → ZWalk _ _ (zinL (lX a) Z)) (e-sU a b) j)
    reach-sound (go (syncBᴾ {a = a} {b} mt i) r) with reach-sound r
    ... | u , u′ , f , g , j = a ∷ u , b ∷ u′ , f , g , zsyncB mt (inh⇑ (e-sB a b) i) j
    reach-sound (go (firstLᴾ {a = a} {b} {I} mt i₁ i₂) r) with reach-sound r
    ... | u , u′ , f , g , j =
      a ∷ u , u′ , f , g ,
      zfirstL mt (inh⇑ (sc-Aᴸ a) i₁) (inh⇑ (e-fL a b I) i₂) (subst (λ Z → ZWalk _ _ (zinU (lY b) Z)) (e-fL a b I) j)
    reach-sound (go (lateUᴾ {a = a} {b} {I} mt i₁ i₂ i₃) r) with reach-sound r
    ... | u , u′ , f , g , j =
      a ∷ u , u′ , f , g ,
      zlateU mt (inh⇑ (sc-Aᵁ b) i₁) (inh⇑ (trans (sc-⊖ (Aᵁᴺ b) I) (cong (_⊖ᶻ scZ I) (sc-Aᵁ b))) i₂)
             (inh⇑ (e-lU a b I) i₃) (subst (λ Z → ZWalk _ _ (zinL (lX a) Z)) (e-lU a b I) j)
    reach-sound (go (bothUᴾ {a = a} {b} {I} mt i₁ i₂) r) with reach-sound r
    ... | u , u′ , f , g , j = a ∷ u , u′ , f , g , zbothU mt (inh⇑ (sc-Aᴸ a) i₁) (inh⇑ (e-bU a b I) i₂) j
    reach-sound (go (firstUᴾ {a = a} {b} {I} mt i₁ i₂) r) with reach-sound r
    ... | u , u′ , f , g , j =
      u , b ∷ u′ , f , g ,
      zfirstU mt (inh⇑ (sc-Aᵁ b) i₁) (inh⇑ (e-fU a b I) i₂) (subst (λ Z → ZWalk _ _ (zinL (lX a) Z)) (e-fU a b I) j)
    reach-sound (go (lateLᴾ {a = a} {b} {I} mt i₁ i₂ i₃) r) with reach-sound r
    ... | u , u′ , f , g , j =
      u , b ∷ u′ , f , g ,
      zlateL mt (inh⇑ (sc-Aᴸ a) i₁) (inh⇑ (trans (sc-⊖ (Aᴸᴺ a) I) (cong (_⊖ᶻ scZ I) (sc-Aᴸ a))) i₂)
             (inh⇑ (e-lL a b I) i₃) (subst (λ Z → ZWalk _ _ (zinU (lY b) Z)) (e-lL a b I) j)
    reach-sound (go (bothLᴾ {a = a} {b} {I} mt i₁ i₂) r) with reach-sound r
    ... | u , u′ , f , g , j = u , b ∷ u′ , f , g , zbothL mt (inh⇑ (sc-Aᵁ b) i₁) (inh⇑ (e-bL a b I) i₂) j

    ----------------------------------------------------------------------
    -- Walks on zones are paths of moves

    data Rel : ZPhase → Ph → Set where
      rs : Rel zsync zs
      rl : ∀ {a I J} → scZ I ≡ J → Rel (zinL (lX a) J) (zl a I)
      ru : ∀ {b I J} → scZ I ≡ J → Rel (zinU (lY b) J) (zu b I)

    private
      relL : ∀ {φ ζ} → Rel ζ φ → ZAtL ζ → AtLᴾ φ
      relL rs     zsync = zs
      relL (ru _) zinU  = zu

      relU : ∀ {φ ζ} → Rel ζ φ → ZAtU ζ → AtUᴾ φ
      relU rs     zsync = zs
      relU (rl _) zinL  = zl

      ∷-inj : ∀ {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y × xs ≡ ys
      ∷-inj refl = refl , refl

    reach-complete : ∀ {v w ζ} → ZWalk v w ζ → ∀ {p q φ u u′}
                   → v ≡ map lX u → w ≡ map lY u′ → Rel ζ φ → AccX p u → AccY q u′ → Reach (p , q , φ)
    reach-complete zdone {u = []} {[]} refl refl rs f g = stop f g
    reach-complete zdone {u = []} {_ ∷ _} _ () _ _ _
    reach-complete zdone {u = _ ∷ _} () _ _ _ _
    reach-complete (zskipL at z j) {u = a ∷ u₀} ev ew rel f g with ∷-inj ev
    ... | ea , ev′ = go (skipLᴾ (relL rel at) (subst ZeroL ea z)) (reach-complete j ev′ ew rel f g)
    reach-complete (zskipU at z j) {u′ = b ∷ u₀} ev ew rel f g with ∷-inj ew
    ... | eb , ew′ = go (skipUᴾ (relU rel at) (subst ZeroU eb z)) (reach-complete j ev ew′ rel f g)
    reach-complete (zopop {o} i j) {u = a ∷ u₀} {b ∷ u₀′} ev ew rs f g with ∷-inj ev | ∷-inj ew
    ... | ea , ev′ | eb , ew′ =
      go (opopᴾ (o , sym ea , sym eb))
         (reach-complete j ev′ ew′ rs f g)
    reach-complete (zsyncL mt iA iN j) {u = a ∷ u₀} {b ∷ u₀′} refl refl rs f g =
      go (syncLᴾ mt (inh⇓ (sc-Aᴸ a) iA) (inh⇓ (e-sL a b) iN)) (reach-complete j refl refl (ru (e-sL a b)) f g)
    reach-complete (zsyncU mt iA iN j) {u = a ∷ u₀} {b ∷ u₀′} refl refl rs f g =
      go (syncUᴾ mt (inh⇓ (sc-Aᵁ b) iA) (inh⇓ (e-sU a b) iN)) (reach-complete j refl refl (rl (e-sU a b)) f g)
    reach-complete (zsyncB mt i j) {u = a ∷ u₀} {b ∷ u₀′} refl refl rs f g =
      go (syncBᴾ mt (inh⇓ (e-sB a b) i)) (reach-complete j refl refl rs f g)
    reach-complete (zfirstL mt iA iN j) {u = a ∷ u₀} refl refl (ru {b} {N} refl) f g =
      go (firstLᴾ mt (inh⇓ (sc-Aᴸ a) iA) (inh⇓ (e-fL a b N) iN))
         (reach-complete j refl refl (ru (e-fL a b N)) f g)
    reach-complete (zlateU mt iA iD iN j) {u = a ∷ u₀} refl refl (ru {b} {N} refl) f g =
      go (lateUᴾ mt (inh⇓ (sc-Aᵁ b) iA) (inh⇓ (trans (sc-⊖ (Aᵁᴺ b) N) (cong (_⊖ᶻ scZ N) (sc-Aᵁ b))) iD)
                 (inh⇓ (e-lU a b N) iN))
         (reach-complete j refl refl (rl (e-lU a b N)) f g)
    reach-complete (zbothU mt iA iX j) {u = a ∷ u₀} refl refl (ru {b} {N} refl) f g =
      go (bothUᴾ mt (inh⇓ (sc-Aᴸ a) iA) (inh⇓ (e-bU a b N) iX)) (reach-complete j refl refl rs f g)
    reach-complete (zfirstU mt iA iN j) {u′ = b ∷ u₀′} refl refl (rl {a} {N} refl) f g =
      go (firstUᴾ mt (inh⇓ (sc-Aᵁ b) iA) (inh⇓ (e-fU a b N) iN))
         (reach-complete j refl refl (rl (e-fU a b N)) f g)
    reach-complete (zlateL mt iA iD iN j) {u′ = b ∷ u₀′} refl refl (rl {a} {N} refl) f g =
      go (lateLᴾ mt (inh⇓ (sc-Aᴸ a) iA) (inh⇓ (trans (sc-⊖ (Aᴸᴺ a) N) (cong (_⊖ᶻ scZ N) (sc-Aᴸ a))) iD)
                 (inh⇓ (e-lL a b N) iN))
         (reach-complete j refl refl (ru (e-lL a b N)) f g)
    reach-complete (zbothL mt iA iX j) {u′ = b ∷ u₀′} refl refl (rl {a} {N} refl) f g =
      go (bothLᴾ mt (inh⇓ (sc-Aᵁ b) iA) (inh⇓ (e-bL a b N) iX)) (reach-complete j refl refl rs f g)

    ----------------------------------------------------------------------
    -- The moves from a state, listed

    private
      guard : ∀ {P : Set} → Dec P → State → List State
      guard (yes _) s = s ∷ []
      guard (no _)  _ = []

      guard⁺ : ∀ {P : Set} (d : Dec P) {s} → P → s ∈ˡ guard d s
      guard⁺ (yes _) _ = here refl
      guard⁺ (no ¬p) p = ⊥-elim (¬p p)

      guard⁻ : ∀ {P : Set} (d : Dec P) {s s′} → s′ ∈ˡ guard d s → P × s′ ≡ s
      guard⁻ (yes p) (here e) = p , e

    startsᴾ : ℕ → ℕ → Fin kX → Fin kY → List State
    startsᴾ p q a b =
         guard (opop? a b) (nx p a , ny q b , zs)
      ++ guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? (normᵁᴺ b (Aᴸᴺ a)))
               (nx p a , ny q b , zu b (normᵁᴺ b (Aᴸᴺ a)))
      ++ guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? (normᴸᴺ a (Aᵁᴺ b)))
               (nx p a , ny q b , zl a (normᴸᴺ a (Aᵁᴺ b)))
      ++ guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a Z.∩ᶻ Aᵁᴺ b))
               (nx p a , ny q b , zs)

    insideᵁ : ℕ → ℕ → Fin kY → Z.Zone → Fin kX → List State
    insideᵁ p q b I a =
         guard (zeroL? a) (nx p a , q , zu b I)
      ++ guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? (normᵁᴺ b (I Z.⊕ᶻ Aᴸᴺ a)))
               (nx p a , q , zu b (normᵁᴺ b (I Z.⊕ᶻ Aᴸᴺ a)))
      ++ guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? (Aᵁᴺ b Z.⊖ᶻ I)
                  ×-dec Z.Inh? (normᴸᴺ a (Aᵁᴺ b Z.⊖ᶻ I)))
               (nx p a , q , zl a (normᴸᴺ a (Aᵁᴺ b Z.⊖ᶻ I)))
      ++ guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? ((I Z.⊕ᶻ Aᴸᴺ a) Z.∩ᶻ Aᵁᴺ b))
               (nx p a , q , zs)

    insideᴸ : ℕ → ℕ → Fin kX → Z.Zone → Fin kY → List State
    insideᴸ p q a I b =
         guard (zeroU? b) (p , ny q b , zl a I)
      ++ guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? (normᴸᴺ a (I Z.⊕ᶻ Aᵁᴺ b)))
               (p , ny q b , zl a (normᴸᴺ a (I Z.⊕ᶻ Aᵁᴺ b)))
      ++ guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? (Aᴸᴺ a Z.⊖ᶻ I)
                  ×-dec Z.Inh? (normᵁᴺ b (Aᴸᴺ a Z.⊖ᶻ I)))
               (p , ny q b , zu b (normᵁᴺ b (Aᴸᴺ a Z.⊖ᶻ I)))
      ++ guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? ((I Z.⊕ᶻ Aᵁᴺ b) Z.∩ᶻ Aᴸᴺ a))
               (p , ny q b , zs)

    succ : State → List State
    succ (p , q , zs) =
         concatMap (λ a → guard (zeroL? a) (nx p a , q , zs)) (allFin kX)
      ++ concatMap (λ b → guard (zeroU? b) (p , ny q b , zs)) (allFin kY)
      ++ concatMap (λ a → concatMap (startsᴾ p q a) (allFin kY)) (allFin kX)
    succ (p , q , zu b I) = concatMap (insideᵁ p q b I) (allFin kX)
    succ (p , q , zl a I) = concatMap (insideᴸ p q a I) (allFin kY)

    private
      open import Data.List.Membership.Propositional.Properties
        using (∈-++⁻; ∈-concatMap⁺; ∈-concatMap⁻)
      open import Data.List.Membership.Propositional using (find; lose)

      cm⁻ : ∀ {A : Set} (f : A → List State) xs {s} → s ∈ˡ concatMap f xs → Σ[ x ∈ A ] s ∈ˡ f x
      cm⁻ f xs m with find (∈-concatMap⁻ f {xs = xs} m)
      ... | x , _ , m′ = x , m′

      cm⁺ : ∀ {A : Set} (f : A → List State) {xs x s} → x ∈ˡ xs → s ∈ˡ f x → s ∈ˡ concatMap f xs
      cm⁺ f x∈ m = ∈-concatMap⁺ f (lose x∈ m)

      l⁺ : ∀ {xs ys : List State} {s} → s ∈ˡ xs → s ∈ˡ xs ++ ys
      l⁺ = ∈-++⁺ˡ

      r⁺ : ∀ (xs : List State) {ys s} → s ∈ˡ ys → s ∈ˡ xs ++ ys
      r⁺ xs = ∈-++⁺ʳ xs

    -- a listed move is a move, and every move is listed

    private
      split4 : ∀ {P₁ P₂ P₃ P₄ : Set} (d₁ : Dec P₁) (d₂ : Dec P₂) (d₃ : Dec P₃) (d₄ : Dec P₄) s₁ s₂ s₃ s₄ {s′}
             → s′ ∈ˡ guard d₁ s₁ ++ guard d₂ s₂ ++ guard d₃ s₃ ++ guard d₄ s₄
             → (P₁ × s′ ≡ s₁) ⊎ (P₂ × s′ ≡ s₂) ⊎ (P₃ × s′ ≡ s₃) ⊎ (P₄ × s′ ≡ s₄)
      split4 (yes p₁) d₂ d₃ d₄ s₁ s₂ s₃ s₄ (here e) = inj₁ (p₁ , e)
      split4 (yes p₁) d₂ d₃ d₄ s₁ s₂ s₃ s₄ (there m) = inj₂ (split3 d₂ d₃ d₄ s₂ s₃ s₄ m)
        where
          split3 : ∀ {P₂ P₃ P₄ : Set} (d₂ : Dec P₂) (d₃ : Dec P₃) (d₄ : Dec P₄) s₂ s₃ s₄ {s′}
                 → s′ ∈ˡ guard d₂ s₂ ++ guard d₃ s₃ ++ guard d₄ s₄
                 → (P₂ × s′ ≡ s₂) ⊎ (P₃ × s′ ≡ s₃) ⊎ (P₄ × s′ ≡ s₄)
          split3 (yes p₂) d₃ d₄ s₂ s₃ s₄ (here e)  = inj₁ (p₂ , e)
          split3 (yes p₂) d₃ d₄ s₂ s₃ s₄ (there m) = inj₂ (split2 d₃ d₄ s₃ s₄ m)
            where
              split2 : ∀ {P₃ P₄ : Set} (d₃ : Dec P₃) (d₄ : Dec P₄) s₃ s₄ {s′}
                     → s′ ∈ˡ guard d₃ s₃ ++ guard d₄ s₄ → (P₃ × s′ ≡ s₃) ⊎ (P₄ × s′ ≡ s₄)
              split2 (yes p₃) d₄ s₃ s₄ (here e)  = inj₁ (p₃ , e)
              split2 (yes p₃) d₄ s₃ s₄ (there m) = inj₂ (guard⁻ d₄ m)
              split2 (no _)   d₄ s₃ s₄ m         = inj₂ (guard⁻ d₄ m)
          split3 (no _) d₃ d₄ s₂ s₃ s₄ m = inj₂ (split2′ d₃ d₄ s₃ s₄ m)
            where
              split2′ : ∀ {P₃ P₄ : Set} (d₃ : Dec P₃) (d₄ : Dec P₄) s₃ s₄ {s′}
                      → s′ ∈ˡ guard d₃ s₃ ++ guard d₄ s₄ → (P₃ × s′ ≡ s₃) ⊎ (P₄ × s′ ≡ s₄)
              split2′ (yes p₃) d₄ s₃ s₄ (here e)  = inj₁ (p₃ , e)
              split2′ (yes p₃) d₄ s₃ s₄ (there m) = inj₂ (guard⁻ d₄ m)
              split2′ (no _)   d₄ s₃ s₄ m         = inj₂ (guard⁻ d₄ m)
      split4 (no _) d₂ d₃ d₄ s₁ s₂ s₃ s₄ m = inj₂ (split3′ d₂ d₃ d₄ s₂ s₃ s₄ m)
        where
          split3′ : ∀ {P₂ P₃ P₄ : Set} (d₂ : Dec P₂) (d₃ : Dec P₃) (d₄ : Dec P₄) s₂ s₃ s₄ {s′}
                  → s′ ∈ˡ guard d₂ s₂ ++ guard d₃ s₃ ++ guard d₄ s₄
                  → (P₂ × s′ ≡ s₂) ⊎ (P₃ × s′ ≡ s₃) ⊎ (P₄ × s′ ≡ s₄)
          split3′ d₂ d₃ d₄ s₂ s₃ s₄ m with ∈-++⁻ (guard d₂ s₂) m
          ... | inj₁ m₁ = inj₁ (guard⁻ d₂ m₁)
          ... | inj₂ m₁ with ∈-++⁻ (guard d₃ s₃) m₁
          ...   | inj₁ m₂ = inj₂ (inj₁ (guard⁻ d₃ m₂))
          ...   | inj₂ m₂ = inj₂ (inj₂ (guard⁻ d₄ m₂))

      start-step : ∀ p q a b {s′} → s′ ∈ˡ startsᴾ p q a b → Step (p , q , zs) s′
      start-step p q a b m with split4
        (opop? a b)
        (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? (normᵁᴺ b (Aᴸᴺ a)))
        (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? (normᴸᴺ a (Aᵁᴺ b)))
        (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a Z.∩ᶻ Aᵁᴺ b))
        (nx p a , ny q b , zs) (nx p a , ny q b , zu b (normᵁᴺ b (Aᴸᴺ a)))
        (nx p a , ny q b , zl a (normᴸᴺ a (Aᵁᴺ b))) (nx p a , ny q b , zs) m
      ... | inj₁ (oo , refl)                              = opopᴾ oo
      ... | inj₂ (inj₁ ((mt , i₁ , i₂) , refl))           = syncLᴾ mt i₁ i₂
      ... | inj₂ (inj₂ (inj₁ ((mt , i₁ , i₂) , refl)))    = syncUᴾ mt i₁ i₂
      ... | inj₂ (inj₂ (inj₂ ((mt , i) , refl)))          = syncBᴾ mt i

      insideᵁ-step : ∀ p q b I a {s′} → s′ ∈ˡ insideᵁ p q b I a → Step (p , q , zu b I) s′
      insideᵁ-step p q b I a m with split4
        (zeroL? a)
        (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? (normᵁᴺ b (I Z.⊕ᶻ Aᴸᴺ a)))
        (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? (Aᵁᴺ b Z.⊖ᶻ I)
           ×-dec Z.Inh? (normᴸᴺ a (Aᵁᴺ b Z.⊖ᶻ I)))
        (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? ((I Z.⊕ᶻ Aᴸᴺ a) Z.∩ᶻ Aᵁᴺ b))
        (nx p a , q , zu b I) (nx p a , q , zu b (normᵁᴺ b (I Z.⊕ᶻ Aᴸᴺ a)))
        (nx p a , q , zl a (normᴸᴺ a (Aᵁᴺ b Z.⊖ᶻ I))) (nx p a , q , zs) m
      ... | inj₁ (z , refl)                                  = skipLᴾ zu z
      ... | inj₂ (inj₁ ((mt , i₁ , i₂) , refl))              = firstLᴾ mt i₁ i₂
      ... | inj₂ (inj₂ (inj₁ ((mt , i₁ , i₂ , i₃) , refl)))  = lateUᴾ mt i₁ i₂ i₃
      ... | inj₂ (inj₂ (inj₂ ((mt , i₁ , i₂) , refl)))       = bothUᴾ mt i₁ i₂

      insideᴸ-step : ∀ p q a I b {s′} → s′ ∈ˡ insideᴸ p q a I b → Step (p , q , zl a I) s′
      insideᴸ-step p q a I b m with split4
        (zeroU? b)
        (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? (normᴸᴺ a (I Z.⊕ᶻ Aᵁᴺ b)))
        (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? (Aᴸᴺ a Z.⊖ᶻ I)
           ×-dec Z.Inh? (normᵁᴺ b (Aᴸᴺ a Z.⊖ᶻ I)))
        (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? ((I Z.⊕ᶻ Aᵁᴺ b) Z.∩ᶻ Aᴸᴺ a))
        (p , ny q b , zl a I) (p , ny q b , zl a (normᴸᴺ a (I Z.⊕ᶻ Aᵁᴺ b)))
        (p , ny q b , zu b (normᵁᴺ b (Aᴸᴺ a Z.⊖ᶻ I))) (p , ny q b , zs) m
      ... | inj₁ (z , refl)                                  = skipUᴾ zl z
      ... | inj₂ (inj₁ ((mt , i₁ , i₂) , refl))              = firstUᴾ mt i₁ i₂
      ... | inj₂ (inj₂ (inj₁ ((mt , i₁ , i₂ , i₃) , refl)))  = lateLᴾ mt i₁ i₂ i₃
      ... | inj₂ (inj₂ (inj₂ ((mt , i₁ , i₂) , refl)))       = bothLᴾ mt i₁ i₂

    ∈-step : ∀ s {s′} → s′ ∈ˡ succ s → Step s s′
    ∈-step (p , q , zs) m
      with ∈-++⁻ (concatMap (λ a → guard (zeroL? a) (nx p a , q , zs)) (allFin kX)) m
    ... | inj₁ m₁ with cm⁻ (λ a → guard (zeroL? a) (nx p a , q , zs)) (allFin kX) m₁
    ...   | a , m₂ with guard⁻ (zeroL? a) m₂
    ...     | z , refl = skipLᴾ zs z
    ∈-step (p , q , zs) m | inj₂ m₁
      with ∈-++⁻ (concatMap (λ b → guard (zeroU? b) (p , ny q b , zs)) (allFin kY)) m₁
    ... | inj₁ m₂ with cm⁻ (λ b → guard (zeroU? b) (p , ny q b , zs)) (allFin kY) m₂
    ...   | b , m₃ with guard⁻ (zeroU? b) m₃
    ...     | z , refl = skipUᴾ zs z
    ∈-step (p , q , zs) m | inj₂ m₁ | inj₂ m₂
      with cm⁻ (λ a → concatMap (startsᴾ p q a) (allFin kY)) (allFin kX) m₂
    ... | a , m₃ with cm⁻ (startsᴾ p q a) (allFin kY) m₃
    ...   | b , m₄ = start-step p q a b m₄
    ∈-step (p , q , zu b I) m with cm⁻ (insideᵁ p q b I) (allFin kX) m
    ... | a , m₁ = insideᵁ-step p q b I a m₁
    ∈-step (p , q , zl a I) m with cm⁻ (insideᴸ p q a I) (allFin kY) m
    ... | b , m₁ = insideᴸ-step p q a I b m₁

    -- the parts of the lists, named

    skL : ℕ → ℕ → Ph → Fin kX → List State
    skL p q φ a = guard (zeroL? a) (nx p a , q , φ)

    skU : ℕ → ℕ → Ph → Fin kY → List State
    skU p q φ b = guard (zeroU? b) (p , ny q b , φ)

    allL : ℕ → ℕ → List State
    allL p q = concatMap (skL p q zs) (allFin kX)

    allU : ℕ → ℕ → List State
    allU p q = concatMap (skU p q zs) (allFin kY)

    g-oo : ℕ → ℕ → Fin kX → Fin kY → List State
    g-oo p q a b = guard (opop? a b) (nx p a , ny q b , zs)

    g-sL : ℕ → ℕ → Fin kX → Fin kY → List State
    g-sL p q a b = guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? (normᵁᴺ b (Aᴸᴺ a)))
                         (nx p a , ny q b , zu b (normᵁᴺ b (Aᴸᴺ a)))

    g-sU : ℕ → ℕ → Fin kX → Fin kY → List State
    g-sU p q a b = guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? (normᴸᴺ a (Aᵁᴺ b)))
                         (nx p a , ny q b , zl a (normᴸᴺ a (Aᵁᴺ b)))

    g-fL : ℕ → ℕ → Fin kY → Z.Zone → Fin kX → List State
    g-fL p q b I a = guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? (normᵁᴺ b (I Z.⊕ᶻ Aᴸᴺ a)))
                           (nx p a , q , zu b (normᵁᴺ b (I Z.⊕ᶻ Aᴸᴺ a)))

    g-lU : ℕ → ℕ → Fin kY → Z.Zone → Fin kX → List State
    g-lU p q b I a = guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? (Aᵁᴺ b Z.⊖ᶻ I)
                              ×-dec Z.Inh? (normᴸᴺ a (Aᵁᴺ b Z.⊖ᶻ I)))
                           (nx p a , q , zl a (normᴸᴺ a (Aᵁᴺ b Z.⊖ᶻ I)))

    g-fU : ℕ → ℕ → Fin kX → Z.Zone → Fin kY → List State
    g-fU p q a I b = guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? (normᴸᴺ a (I Z.⊕ᶻ Aᵁᴺ b)))
                           (p , ny q b , zl a (normᴸᴺ a (I Z.⊕ᶻ Aᵁᴺ b)))

    g-lL : ℕ → ℕ → Fin kX → Z.Zone → Fin kY → List State
    g-lL p q a I b = guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? (Aᴸᴺ a Z.⊖ᶻ I)
                              ×-dec Z.Inh? (normᵁᴺ b (Aᴸᴺ a Z.⊖ᶻ I)))
                           (p , ny q b , zu b (normᵁᴺ b (Aᴸᴺ a Z.⊖ᶻ I)))

    step-∈ : ∀ {s s′} → Step s s′ → s′ ∈ˡ succ s
    step-∈ (skipLᴾ {p} {q} {a = a} zs z) = l⁺ (cm⁺ (skL p q zs) (∈-allFin a) (guard⁺ (zeroL? a) z))
    step-∈ (skipLᴾ {p} {q} {zu b I} {a} zu z) = cm⁺ (insideᵁ p q b I) (∈-allFin a) (l⁺ (guard⁺ (zeroL? a) z))
    step-∈ (skipUᴾ {p} {q} {b = b} zs z) = r⁺ (allL p q) (l⁺ (cm⁺ (skU p q zs) (∈-allFin b) (guard⁺ (zeroU? b) z)))
    step-∈ (skipUᴾ {p} {q} {zl a I} {b} zl z) = cm⁺ (insideᴸ p q a I) (∈-allFin b) (l⁺ (guard⁺ (zeroU? b) z))
    step-∈ (opopᴾ {p} {q} {a} {b} oo) =
      r⁺ (allL p q) (r⁺ (allU p q) (cm⁺ (λ a → concatMap (startsᴾ p q a) (allFin kY)) (∈-allFin a)
        (cm⁺ (startsᴾ p q a) (∈-allFin b) (l⁺ (guard⁺ (opop? a b) oo)))))
    step-∈ (syncLᴾ {p} {q} {a} {b} mt i₁ i₂) =
      r⁺ (allL p q) (r⁺ (allU p q) (cm⁺ (λ a → concatMap (startsᴾ p q a) (allFin kY)) (∈-allFin a)
        (cm⁺ (startsᴾ p q a) (∈-allFin b)
          (r⁺ (g-oo p q a b) (l⁺ (guard⁺ (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? (normᵁᴺ b (Aᴸᴺ a)))
                                         (mt , i₁ , i₂)))))))
    step-∈ (syncUᴾ {p} {q} {a} {b} mt i₁ i₂) =
      r⁺ (allL p q) (r⁺ (allU p q) (cm⁺ (λ a → concatMap (startsᴾ p q a) (allFin kY)) (∈-allFin a)
        (cm⁺ (startsᴾ p q a) (∈-allFin b)
          (r⁺ (g-oo p q a b) (r⁺ (g-sL p q a b)
            (l⁺ (guard⁺ (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? (normᴸᴺ a (Aᵁᴺ b)))
                        (mt , i₁ , i₂))))))))
    step-∈ (syncBᴾ {p} {q} {a} {b} mt i) =
      r⁺ (allL p q) (r⁺ (allU p q) (cm⁺ (λ a → concatMap (startsᴾ p q a) (allFin kY)) (∈-allFin a)
        (cm⁺ (startsᴾ p q a) (∈-allFin b)
          (r⁺ (g-oo p q a b) (r⁺ (g-sL p q a b) (r⁺ (g-sU p q a b)
            (guard⁺ (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a Z.∩ᶻ Aᵁᴺ b)) (mt , i))))))))
    step-∈ (firstLᴾ {p} {q} {a} {b} {I} mt i₁ i₂) =
      cm⁺ (insideᵁ p q b I) (∈-allFin a)
        (r⁺ (skL p q (zu b I) a)
          (l⁺ (guard⁺ (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? (normᵁᴺ b (I Z.⊕ᶻ Aᴸᴺ a)))
                      (mt , i₁ , i₂))))
    step-∈ (lateUᴾ {p} {q} {a} {b} {I} mt i₁ i₂ i₃) =
      cm⁺ (insideᵁ p q b I) (∈-allFin a)
        (r⁺ (skL p q (zu b I) a) (r⁺ (g-fL p q b I a)
          (l⁺ (guard⁺ (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? (Aᵁᴺ b Z.⊖ᶻ I)
                         ×-dec Z.Inh? (normᴸᴺ a (Aᵁᴺ b Z.⊖ᶻ I)))
                      (mt , i₁ , i₂ , i₃)))))
    step-∈ (bothUᴾ {p} {q} {a} {b} {I} mt i₁ i₂) =
      cm⁺ (insideᵁ p q b I) (∈-allFin a)
        (r⁺ (skL p q (zu b I) a) (r⁺ (g-fL p q b I a) (r⁺ (g-lU p q b I a)
          (guard⁺ (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? ((I Z.⊕ᶻ Aᴸᴺ a) Z.∩ᶻ Aᵁᴺ b))
                  (mt , i₁ , i₂)))))
    step-∈ (firstUᴾ {p} {q} {a} {b} {I} mt i₁ i₂) =
      cm⁺ (insideᴸ p q a I) (∈-allFin b)
        (r⁺ (skU p q (zl a I) b)
          (l⁺ (guard⁺ (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? (normᴸᴺ a (I Z.⊕ᶻ Aᵁᴺ b)))
                      (mt , i₁ , i₂))))
    step-∈ (lateLᴾ {p} {q} {a} {b} {I} mt i₁ i₂ i₃) =
      cm⁺ (insideᴸ p q a I) (∈-allFin b)
        (r⁺ (skU p q (zl a I) b) (r⁺ (g-fU p q a I b)
          (l⁺ (guard⁺ (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? (Aᴸᴺ a Z.⊖ᶻ I)
                         ×-dec Z.Inh? (normᵁᴺ b (Aᴸᴺ a Z.⊖ᶻ I)))
                      (mt , i₁ , i₂ , i₃)))))
    step-∈ (bothLᴾ {p} {q} {a} {b} {I} mt i₁ i₂) =
      cm⁺ (insideᴸ p q a I) (∈-allFin b)
        (r⁺ (skU p q (zl a I) b) (r⁺ (g-fU p q a I b) (r⁺ (g-lL p q a I b)
          (guard⁺ (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? ((I Z.⊕ᶻ Aᵁᴺ b) Z.∩ᶻ Aᴸᴺ a))
                  (mt , i₁ , i₂)))))

    ----------------------------------------------------------------------
    -- Normalised zones are bounded by the largest count

    private
      maxs : List ℕ → ℕ
      maxs = foldr ℕ._⊔_ 0

      ≤-maxs : ∀ {x} xs → x ∈ˡ xs → x ℕ.≤ maxs xs
      ≤-maxs (y ∷ ys) (here refl) = ℕ.m≤m⊔n y (maxs ys)
      ≤-maxs (y ∷ ys) (there m)   = ℕ.≤-trans (≤-maxs ys m) (ℕ.m≤n⊔m y (maxs ys))

    endᴸ : Fin kX → ℕ
    endᴸ a with lX a
    ... | op _   = 0
    ... | st _ c = count (pt c)

    endᵁ : Fin kY → ℕ
    endᵁ b with lY b
    ... | op _         = 0
    ... | st _ (fin c) = count (pt c)
    ... | st _ ∞       = 0

    endʳ : Fin n → ℕ
    endʳ c = count (ptʰ (hi (rt (name c))))

    ends : List ℕ
    ends = map endᴸ (allFin kX) ++ map endᵁ (allFin kY) ++ map endʳ (allFin n)

    K : ℕ
    K = maxs ends

    private
      ≤K-L : ∀ a → endᴸ a ℕ.≤ K
      ≤K-L a = ≤-maxs ends (∈-++⁺ˡ (∈-map⁺ endᴸ (∈-allFin a)))

      ≤K-U : ∀ b → endᵁ b ℕ.≤ K
      ≤K-U b = ≤-maxs ends (∈-++⁺ʳ (map endᴸ (allFin kX)) (∈-++⁺ˡ (∈-map⁺ endᵁ (∈-allFin b))))

      ≤K-r : ∀ o → count (ptʰ (hi (rt o))) ℕ.≤ K
      ≤K-r o = subst (λ o′ → count (ptʰ (hi (rt o′))) ℕ.≤ K) (name-code o)
                 (≤-maxs ends (∈-++⁺ʳ (map endᴸ (allFin kX)) (∈-++⁺ʳ (map endᵁ (allFin kY))
                    (∈-map⁺ endʳ (∈-allFin (code o))))))

    BH : N.Hi → Set
    BH (N.fin c) = N.pt c ℕ.≤ K
    BH N.∞       = ⊤

    BZ : Z.Zone → Set
    BZ Z = N.pt (Z.loᶻ Z) ℕ.≤ K × BH (Z.hiᶻ Z)

    private
      hi-fin : ∀ {h c} → h N.⊑ʰ N.fin c → Σ[ c′ ∈ N.Cut ] h ≡ N.fin c′ × N.pt c′ ℕ.≤ N.pt c
      hi-fin {N.fin c′} r = c′ , refl , N.⊑⇒≤ r
      hi-fin {N.∞}      ()

      bz-fin : ∀ {Z c} → Z.Inh Z → Z.hiᶻ Z N.⊑ʰ N.fin c → N.pt c ℕ.≤ K → BZ Z
      bz-fin {Z.⟨ l , h ⟩ᶻ} i r k with hi-fin {h} r
      ... | c′ , refl , le = ℕ.≤-trans (N.⊑⇒≤ (N.⊏⇒⊑ i)) (ℕ.≤-trans le k) , ℕ.≤-trans le k

      -- the upper end of the running time of an operation, in counts
      rt-hi : ∀ o → Σ[ c ∈ N.Cut ] downʰ (hi (rt o)) ≡ N.fin c × N.pt c ℕ.≤ K
      rt-hi o with hi (rt o) | rt-bounded o | ≤K-r o
      ... | fin (p ∣ᶜ s) | bfin _ | k = (count p N.∣ sideℕ s) , refl , k

      bz-rt : ∀ o I → Z.Inh (I Z.∩ᶻ Z.⟨ N.0⁻ , downʰ (hi (rt o)) ⟩ᶻ) → BZ (I Z.∩ᶻ Z.⟨ N.0⁻ , downʰ (hi (rt o)) ⟩ᶻ)
      bz-rt o I i with rt-hi o
      ... | c , e , k =
        bz-fin {I Z.∩ᶻ Z.⟨ N.0⁻ , downʰ (hi (rt o)) ⟩ᶻ} i
          (subst (λ h → Z.hiᶻ I Z.⊓ʰ h N.⊑ʰ N.fin c) (sym e) (Z.⊓ʰ-lbʳ (Z.hiᶻ I) (N.fin c))) k

      raise-cases : ∀ c h → (Z.raise c h ≡ N.∞) ⊎ (Z.raise c h ≡ h × ¬ (c N.◁ h))
      raise-cases c h with c N.◁? h
      ... | yes _ = inj₁ refl
      ... | no ¬p = inj₂ (refl , ¬p)

      ¬◁⇒⊑ : ∀ {c h} → ¬ (c N.◁ h) → h N.⊑ʰ N.fin c
      ¬◁⇒⊑ {c} {N.fin c′} ¬p with c′ N.⊑? c
      ... | yes q = q
      ... | no ¬q = ⊥-elim (¬p ¬q)
      ¬◁⇒⊑ {c} {N.∞} ¬p = ⊥-elim (¬p tt)

    bz-normᴸ : ∀ a I → Z.Inh (normᴸᴺ a I) → BZ (normᴸᴺ a I)
    bz-normᴸ a I i with lX a | ≤K-L a
    ... | op o   | _ = bz-rt o I i
    ... | st S c | k =
      ℕ.≤-trans (N.⊑⇒≤ (N.⊓ᶜ-lbʳ (Z.loᶻ I) (downᶜ c))) k , hiB (raise-cases (downᶜ c) (Z.hiᶻ I))
      where
        hiB : (Z.raise (downᶜ c) (Z.hiᶻ I) ≡ N.∞) ⊎ (Z.raise (downᶜ c) (Z.hiᶻ I) ≡ Z.hiᶻ I × ¬ (downᶜ c N.◁ Z.hiᶻ I))
            → BH (Z.raise (downᶜ c) (Z.hiᶻ I))
        hiB (inj₁ e) = subst BH (sym e) tt
        hiB (inj₂ (e , ¬p)) with hi-fin (¬◁⇒⊑ {downᶜ c} {Z.hiᶻ I} ¬p)
        ... | c′ , e′ , le = subst BH (sym (trans e e′)) (ℕ.≤-trans le k)

    bz-normᵁ : ∀ b I → Z.Inh (normᵁᴺ b I) → BZ (normᵁᴺ b I)
    bz-normᵁ b I i with lY b | ≤K-U b
    ... | op o         | _ = bz-rt o I i
    ... | st S (fin c) | k =
      bz-fin {I Z.∩ᶻ Z.⟨ N.0⁻ , N.fin (downᶜ c) ⟩ᶻ} i (Z.⊓ʰ-lbʳ (Z.hiᶻ I) (N.fin (downᶜ c))) k
    ... | st S ∞       | _ = ℕ.z≤n , tt

    ----------------------------------------------------------------------
    -- Finitely many states

    sides : List N.Side
    sides = N.⁻ ∷ N.⁺ ∷ []

    cutsᴺ : List N.Cut
    cutsᴺ = concatMap (λ k → map (k N.∣_) sides) (upTo (ℕ.suc K))

    hisᴺ : List N.Hi
    hisᴺ = N.∞ ∷ map N.fin cutsᴺ

    zonesᴺ : List Z.Zone
    zonesᴺ = concatMap (λ c → map (Z.⟨ c ,_⟩ᶻ) hisᴺ) cutsᴺ

    phases : List Ph
    phases = zs ∷ concatMap (λ a → map (zl a) zonesᴺ) (allFin kX) ++ concatMap (λ b → map (zu b) zonesᴺ) (allFin kY)

    univ : List State
    univ = concatMap (λ p → concatMap (λ q → map (λ φ → (p , q , φ)) phases) (upTo (AY.size Y′))) (upTo (AX.size X′))

    private
      open import Data.List.Membership.Propositional.Properties using (∈-upTo⁺; ∈-upTo⁻; ∈-map⁻)
      open import Data.List.Membership.Propositional using (find; lose)
      open import Data.List.Membership.Propositional.Properties using (∈-concatMap⁺; ∈-concatMap⁻)

      cmᴬ⁺ : ∀ {A B : Set} (f : A → List B) {xs x y} → x ∈ˡ xs → y ∈ˡ f x → y ∈ˡ concatMap f xs
      cmᴬ⁺ f x∈ m = ∈-concatMap⁺ f (lose x∈ m)

      cmᴬ⁻ : ∀ {A B : Set} (f : A → List B) xs {y} → y ∈ˡ concatMap f xs → Σ[ x ∈ A ] x ∈ˡ xs × y ∈ˡ f x
      cmᴬ⁻ f xs m = find (∈-concatMap⁻ f {xs = xs} m)

      side∈ : ∀ s → s ∈ˡ sides
      side∈ N.⁻ = here refl
      side∈ N.⁺ = there (here refl)

      cut∈ : ∀ {c} → N.pt c ℕ.≤ K → c ∈ˡ cutsᴺ
      cut∈ {k N.∣ s} le = cmᴬ⁺ (λ k → map (k N.∣_) sides) (∈-upTo⁺ (ℕ.s≤s le)) (∈-map⁺ (k N.∣_) (side∈ s))

      hi∈ : ∀ {h} → BH h → h ∈ˡ hisᴺ
      hi∈ {N.fin c} le = there (∈-map⁺ N.fin (cut∈ le))
      hi∈ {N.∞}     _  = here refl

    zone∈ : ∀ {Z} → BZ Z → Z ∈ˡ zonesᴺ
    zone∈ {Z.⟨ c , h ⟩ᶻ} (lc , bh) = cmᴬ⁺ (λ c → map (Z.⟨ c ,_⟩ᶻ) hisᴺ) (cut∈ lc) (∈-map⁺ (Z.⟨ c ,_⟩ᶻ) (hi∈ bh))

    private
      zl∈ : ∀ a {Z} → BZ Z → zl a Z ∈ˡ phases
      zl∈ a b = there (∈-++⁺ˡ (cmᴬ⁺ (λ a → map (zl a) zonesᴺ) (∈-allFin a) (∈-map⁺ (zl a) (zone∈ b))))

      zu∈ : ∀ b {Z} → BZ Z → zu b Z ∈ˡ phases
      zu∈ b bz = there (∈-++⁺ʳ (concatMap (λ a → map (zl a) zonesᴺ) (allFin kX))
                   (cmᴬ⁺ (λ b → map (zu b) zonesᴺ) (∈-allFin b) (∈-map⁺ (zu b) (zone∈ bz))))

      zs∈ : zs ∈ˡ phases
      zs∈ = here refl

      state∈ : ∀ {p q φ} → p ℕ.< AX.size X′ → q ℕ.< AY.size Y′ → φ ∈ˡ phases → (p , q , φ) ∈ˡ univ
      state∈ {p} {q} {φ} p< q< φ∈ =
        cmᴬ⁺ (λ p → concatMap (λ q → map (λ φ → (p , q , φ)) phases) (upTo (AY.size Y′))) (∈-upTo⁺ p<)
          (cmᴬ⁺ (λ q → map (λ φ → (p , q , φ)) phases) (∈-upTo⁺ q<) (∈-map⁺ (λ φ → (p , q , φ)) φ∈))

      state∈⁻ : ∀ {p q φ} → (p , q , φ) ∈ˡ univ → p ℕ.< AX.size X′ × q ℕ.< AY.size Y′ × φ ∈ˡ phases
      state∈⁻ m with cmᴬ⁻ _ (upTo (AX.size X′)) m
      ... | p , p∈ , m′ with cmᴬ⁻ _ (upTo (AY.size Y′)) m′
      ...   | q , q∈ , m″ with ∈-map⁻ _ m″
      ...     | φ , φ∈ , refl = ∈-upTo⁻ p∈ , ∈-upTo⁻ q∈ , φ∈

    open import Grades.Regular.Basics kX using () renaming (next-< to next-<ˣ; start-< to start-<ˣ)
    open import Grades.Regular.Basics kY using () renaming (next-< to next-<ʸ; start-< to start-<ʸ)

    -- a move stays among the states

    private
      step-univ′ : ∀ {p q φ s′} → p ℕ.< AX.size X′ → q ℕ.< AY.size Y′ → φ ∈ˡ phases
                 → Step (p , q , φ) s′ → s′ ∈ˡ univ
      step-univ′ p< q< φ∈ (skipLᴾ {a = a} _ _) = state∈ (next-<ˣ X′ wfX′ p< a) q< φ∈
      step-univ′ p< q< φ∈ (skipUᴾ {b = b} _ _) = state∈ p< (next-<ʸ Y′ wfY′ q< b) φ∈
      step-univ′ p< q< φ∈ (opopᴾ {a = a} {b} _) = state∈ (next-<ˣ X′ wfX′ p< a) (next-<ʸ Y′ wfY′ q< b) zs∈
      step-univ′ p< q< φ∈ (syncLᴾ {a = a} {b} _ _ i) =
        state∈ (next-<ˣ X′ wfX′ p< a) (next-<ʸ Y′ wfY′ q< b) (zu∈ b (bz-normᵁ b (Aᴸᴺ a) i))
      step-univ′ p< q< φ∈ (syncUᴾ {a = a} {b} _ _ i) =
        state∈ (next-<ˣ X′ wfX′ p< a) (next-<ʸ Y′ wfY′ q< b) (zl∈ a (bz-normᴸ a (Aᵁᴺ b) i))
      step-univ′ p< q< φ∈ (syncBᴾ {a = a} {b} _ _) = state∈ (next-<ˣ X′ wfX′ p< a) (next-<ʸ Y′ wfY′ q< b) zs∈
      step-univ′ p< q< φ∈ (firstLᴾ {a = a} {b} {I} _ _ i) =
        state∈ (next-<ˣ X′ wfX′ p< a) q< (zu∈ b (bz-normᵁ b (I Z.⊕ᶻ Aᴸᴺ a) i))
      step-univ′ p< q< φ∈ (lateUᴾ {a = a} {b} {I} _ _ _ i) =
        state∈ (next-<ˣ X′ wfX′ p< a) q< (zl∈ a (bz-normᴸ a (Aᵁᴺ b Z.⊖ᶻ I) i))
      step-univ′ p< q< φ∈ (bothUᴾ {a = a} _ _ _) = state∈ (next-<ˣ X′ wfX′ p< a) q< zs∈
      step-univ′ p< q< φ∈ (firstUᴾ {a = a} {b} {I} _ _ i) =
        state∈ p< (next-<ʸ Y′ wfY′ q< b) (zl∈ a (bz-normᴸ a (I Z.⊕ᶻ Aᵁᴺ b) i))
      step-univ′ p< q< φ∈ (lateLᴾ {a = a} {b} {I} _ _ _ i) =
        state∈ p< (next-<ʸ Y′ wfY′ q< b) (zu∈ b (bz-normᵁ b (Aᴸᴺ a Z.⊖ᶻ I) i))
      step-univ′ p< q< φ∈ (bothLᴾ {b = b} _ _ _) = state∈ p< (next-<ʸ Y′ wfY′ q< b) zs∈

      step-univ″ : ∀ {p q φ s′} → p ℕ.< AX.size X′ × q ℕ.< AY.size Y′ × φ ∈ˡ phases
                 → Step (p , q , φ) s′ → s′ ∈ˡ univ
      step-univ″ (p< , q< , φ∈) = step-univ′ p< q< φ∈

    step-univ : ∀ {p q φ s′} → (p , q , φ) ∈ˡ univ → Step (p , q , φ) s′ → s′ ∈ˡ univ
    step-univ m = step-univ″ (state∈⁻ m)

    start : State
    start = 0 , 0 , zs

    start-univ : start ∈ˡ univ
    start-univ = state∈ (start-<ˣ X′ wfX′) (start-<ʸ Y′ wfY′) zs∈

    ----------------------------------------------------------------------
    -- The moves, reading the tabulated letters

    open Memo M
    open Faithful F

    private
      lXᵐ = lookup vlX
      lYᵐ = lookup vlY
      Aᵐ  = lookup vA
      Bᵐ  = lookup vB

      nLᵐ : Fin kX → Z.Zone → Z.Zone
      nLᵐ a = normL′ (lookup vnL a)

      nUᵐ : Fin kY → Z.Zone → Z.Zone
      nUᵐ b = normU′ (lookup vnU b)

    startsᵐ : ℕ → ℕ → Fin kX → Fin kY → List State
    startsᵐ p q a b =
         guard (opop?′ (lXᵐ a) (lYᵐ b)) (nx p a , ny q b , zs)
      ++ guard (meets? (lXᵐ a) (lYᵐ b) ×-dec Z.Inh? (Aᵐ a) ×-dec Z.Inh? (nUᵐ b (Aᵐ a)))
               (nx p a , ny q b , zu b (nUᵐ b (Aᵐ a)))
      ++ guard (meets? (lXᵐ a) (lYᵐ b) ×-dec Z.Inh? (Bᵐ b) ×-dec Z.Inh? (nLᵐ a (Bᵐ b)))
               (nx p a , ny q b , zl a (nLᵐ a (Bᵐ b)))
      ++ guard (meets? (lXᵐ a) (lYᵐ b) ×-dec Z.Inh? (Aᵐ a Z.∩ᶻ Bᵐ b))
               (nx p a , ny q b , zs)

    insideᵁᵐ : ℕ → ℕ → Fin kY → Z.Zone → Fin kX → List State
    insideᵁᵐ p q b I a =
         guard (T? (lookup vzL a)) (nx p a , q , zu b I)
      ++ guard (meets? (lXᵐ a) (lYᵐ b) ×-dec Z.Inh? (Aᵐ a) ×-dec Z.Inh? (nUᵐ b (I Z.⊕ᶻ Aᵐ a)))
               (nx p a , q , zu b (nUᵐ b (I Z.⊕ᶻ Aᵐ a)))
      ++ guard (meets? (lXᵐ a) (lYᵐ b) ×-dec Z.Inh? (Bᵐ b) ×-dec Z.Inh? (Bᵐ b Z.⊖ᶻ I)
                  ×-dec Z.Inh? (nLᵐ a (Bᵐ b Z.⊖ᶻ I)))
               (nx p a , q , zl a (nLᵐ a (Bᵐ b Z.⊖ᶻ I)))
      ++ guard (meets? (lXᵐ a) (lYᵐ b) ×-dec Z.Inh? (Aᵐ a) ×-dec Z.Inh? ((I Z.⊕ᶻ Aᵐ a) Z.∩ᶻ Bᵐ b))
               (nx p a , q , zs)

    insideᴸᵐ : ℕ → ℕ → Fin kX → Z.Zone → Fin kY → List State
    insideᴸᵐ p q a I b =
         guard (T? (lookup vzU b)) (p , ny q b , zl a I)
      ++ guard (meets? (lXᵐ a) (lYᵐ b) ×-dec Z.Inh? (Bᵐ b) ×-dec Z.Inh? (nLᵐ a (I Z.⊕ᶻ Bᵐ b)))
               (p , ny q b , zl a (nLᵐ a (I Z.⊕ᶻ Bᵐ b)))
      ++ guard (meets? (lXᵐ a) (lYᵐ b) ×-dec Z.Inh? (Aᵐ a) ×-dec Z.Inh? (Aᵐ a Z.⊖ᶻ I)
                  ×-dec Z.Inh? (nUᵐ b (Aᵐ a Z.⊖ᶻ I)))
               (p , ny q b , zu b (nUᵐ b (Aᵐ a Z.⊖ᶻ I)))
      ++ guard (meets? (lXᵐ a) (lYᵐ b) ×-dec Z.Inh? (Bᵐ b) ×-dec Z.Inh? ((I Z.⊕ᶻ Bᵐ b) Z.∩ᶻ Aᵐ a))
               (p , ny q b , zs)

    succᵐ : State → List State
    succᵐ (p , q , zs) =
         concatMap (λ a → guard (T? (lookup vzL a)) (nx p a , q , zs)) (allFin kX)
      ++ concatMap (λ b → guard (T? (lookup vzU b)) (p , ny q b , zs)) (allFin kY)
      ++ concatMap (λ a → concatMap (startsᵐ p q a) (allFin kY)) (allFin kX)
    succᵐ (p , q , zu b I) = concatMap (insideᵁᵐ p q b I) (allFin kX)
    succᵐ (p , q , zl a I) = concatMap (insideᴸᵐ p q a I) (allFin kY)

    -- the same moves

    private
      open import Data.List.Properties using (concatMap-cong)

      guard-T : ∀ {P : Set} (d : Dec P) b s → b ≡ isYes d → guard (T? b) s ≡ guard d s
      guard-T (yes _) _ s refl = refl
      guard-T (no _)  _ s refl = refl

      starts≡ : ∀ p q a b → startsᵐ p q a b ≡ startsᴾ p q a b
      starts≡ p q a b rewrite elX a | elY b | eA a | eB b | enL a | enU b = refl

      insideᵁ≡ : ∀ p q b I a → insideᵁᵐ p q b I a ≡ insideᵁ p q b I a
      insideᵁ≡ p q b I a rewrite elX a | elY b | eA a | eB b | enL a | enU b
        = cong (_++ (g-fL p q b I a ++ g-lU p q b I a
                     ++ guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᴸᴺ a) ×-dec Z.Inh? ((I Z.⊕ᶻ Aᴸᴺ a) Z.∩ᶻ Aᵁᴺ b))
                              (nx p a , q , zs)))
               (guard-T (zeroL? a) (lookup vzL a) _ (ezL a))

      insideᴸ≡ : ∀ p q a I b → insideᴸᵐ p q a I b ≡ insideᴸ p q a I b
      insideᴸ≡ p q a I b rewrite elX a | elY b | eA a | eB b | enL a | enU b
        = cong (_++ (g-fU p q a I b ++ g-lL p q a I b
                     ++ guard (meets? (lX a) (lY b) ×-dec Z.Inh? (Aᵁᴺ b) ×-dec Z.Inh? ((I Z.⊕ᶻ Aᵁᴺ b) Z.∩ᶻ Aᴸᴺ a))
                              (p , ny q b , zs)))
               (guard-T (zeroU? b) (lookup vzU b) _ (ezU b))

    succᵐ≡ : ∀ s → succᵐ s ≡ succ s
    succᵐ≡ (p , q , zs) =
      cong₂ _++_ (concatMap-cong (λ a → guard-T (zeroL? a) (lookup vzL a) _ (ezL a)) (allFin kX))
        (cong₂ _++_ (concatMap-cong (λ b → guard-T (zeroU? b) (lookup vzU b) _ (ezU b)) (allFin kY))
          (concatMap-cong (λ a → concatMap-cong (starts≡ p q a) (allFin kY)) (allFin kX)))
    succᵐ≡ (p , q , zu b I) = concatMap-cong (insideᵁ≡ p q b I) (allFin kX)
    succᵐ≡ (p , q , zl a I) = concatMap-cong (insideᴸ≡ p q a I) (allFin kY)

    ----------------------------------------------------------------------
    -- The search

    private
      open import Relation.Binary.Definitions using (DecidableEquality)
      import Data.Fin.Properties as Fin
      open import Data.Product.Properties using (≡-dec)

      _≟ˢᵈ_ : DecidableEquality N.Side
      N.⁻ ≟ˢᵈ N.⁻ = yes refl
      N.⁺ ≟ˢᵈ N.⁺ = yes refl
      N.⁻ ≟ˢᵈ N.⁺ = no λ ()
      N.⁺ ≟ˢᵈ N.⁻ = no λ ()

      _≟ᶜ_ : DecidableEquality N.Cut
      (p N.∣ s) ≟ᶜ (p′ N.∣ s′) with p ℕ.≟ p′ | s ≟ˢᵈ s′
      ... | yes refl | yes refl = yes refl
      ... | no ¬e    | _        = no λ { refl → ¬e refl }
      ... | _        | no ¬e    = no λ { refl → ¬e refl }

      _≟ʰ_ : DecidableEquality N.Hi
      N.fin c ≟ʰ N.fin c′ with c ≟ᶜ c′
      ... | yes refl = yes refl
      ... | no ¬e    = no λ { refl → ¬e refl }
      N.fin _ ≟ʰ N.∞ = no λ ()
      N.∞ ≟ʰ N.fin _ = no λ ()
      N.∞ ≟ʰ N.∞     = yes refl

      _≟ᶻ_ : DecidableEquality Z.Zone
      Z.⟨ c , h ⟩ᶻ ≟ᶻ Z.⟨ c′ , h′ ⟩ᶻ with c ≟ᶜ c′ | h ≟ʰ h′
      ... | yes refl | yes refl = yes refl
      ... | no ¬e    | _        = no λ { refl → ¬e refl }
      ... | _        | no ¬e    = no λ { refl → ¬e refl }

      _≟ᴾ_ : DecidableEquality Ph
      zs ≟ᴾ zs = yes refl
      zl a I ≟ᴾ zl a′ I′ with a Fin.≟ a′ | I ≟ᶻ I′
      ... | yes refl | yes refl = yes refl
      ... | no ¬e    | _        = no λ { refl → ¬e refl }
      ... | _        | no ¬e    = no λ { refl → ¬e refl }
      zu b I ≟ᴾ zu b′ I′ with b Fin.≟ b′ | I ≟ᶻ I′
      ... | yes refl | yes refl = yes refl
      ... | no ¬e    | _        = no λ { refl → ¬e refl }
      ... | _        | no ¬e    = no λ { refl → ¬e refl }
      zs ≟ᴾ zl _ _ = no λ ()
      zs ≟ᴾ zu _ _ = no λ ()
      zl _ _ ≟ᴾ zs = no λ ()
      zl _ _ ≟ᴾ zu _ _ = no λ ()
      zu _ _ ≟ᴾ zs = no λ ()
      zu _ _ ≟ᴾ zl _ _ = no λ ()

    _≟ˢ_ : DecidableEquality State
    _≟ˢ_ = ≡-dec ℕ._≟_ (≡-dec ℕ._≟_ _≟ᴾ_)

    accept : State → Bool
    accept (p , q , zs)     = AX.isFinal X′ p Data.Bool.Base.∧ AY.isFinal Y′ q
    accept (_ , _ , zl _ _) = false
    accept (_ , _ , zu _ _) = false

    open import Grades.Regular.Basics 0 using (T-∧⁻; T-∧⁺; T-not⁺; T-not⁻)

    private
      ∈-stepᵐ : ∀ s {s′} → s′ ∈ˡ succᵐ s → Step s s′
      ∈-stepᵐ s m = ∈-step s (subst (_ ∈ˡ_) (succᵐ≡ s) m)

      step-∈ᵐ : ∀ {s s′} → Step s s′ → s′ ∈ˡ succᵐ s
      step-∈ᵐ {s} mv = subst (_ ∈ˡ_) (sym (succᵐ≡ s)) (step-∈ mv)

    -- only states from which both tables still accept are kept

    -- a state of a table that is not final and that every letter leaves
    -- unchanged accepts nothing; states of both tables that are not
    -- such sinks are kept

    sinkX : ℕ → Bool
    sinkX p = Data.Bool.Base.not (AX.isFinal X′ p)
      Data.Bool.Base.∧ Data.Bool.ListAction.all (λ a → AX.next X′ p a ℕ.≡ᵇ p) (allFin kX)

    sinkY : ℕ → Bool
    sinkY q = Data.Bool.Base.not (AY.isFinal Y′ q)
      Data.Bool.Base.∧ Data.Bool.ListAction.all (λ b → AY.next Y′ q b ℕ.≡ᵇ q) (allFin kY)

    aliveᵇ : State → Bool
    aliveᵇ (p , q , _) = Data.Bool.Base.not (sinkX p) Data.Bool.Base.∧ Data.Bool.Base.not (sinkY q)

    succᵃ : State → List State
    succᵃ s = filter (λ s′ → T? (aliveᵇ s′)) (succᵐ s)

    private
      open import Data.List.Membership.Propositional.Properties using (∈-filter⁺; ∈-filter⁻)

      ∈-stepᵃ : ∀ s {s′} → s′ ∈ˡ succᵃ s → Step s s′
      ∈-stepᵃ s m = ∈-stepᵐ s (proj₁ (∈-filter⁻ (λ s′ → T? (aliveᵇ s′)) m))

    module R = Grades.Regular.Reach _≟ˢ_ succᵃ accept univ
    module RC = R.Correct (λ { {p , q , φ} c∈ m → step-univ c∈ (∈-stepᵃ _ m) })

    private
      import Data.Bool.ListAction as BL
      open import Data.List.Relation.Unary.All using (All)
      import Data.List.Relation.Unary.All as All

      T-all : ∀ {A : Set} (f : A → Bool) xs → IsTrue (BL.all f xs) → All (λ x → IsTrue (f x)) xs
      T-all f []       _ = All.[]
      T-all f (x ∷ xs) t with f x in e
      ... | true = subst IsTrue (sym e) tt All.∷ T-all f xs t

      -- a sink accepts nothing
      sinkX-dead : ∀ p u → IsTrue (sinkX p) → ¬ AccX p u
      sinkX-dead p u t with T-∧⁻ {Data.Bool.Base.not (AX.isFinal X′ p)} t
      ... | nf , loops = walk u
        where
          stay : ∀ a → AX.next X′ p a ≡ p
          stay a = ℕ.≡ᵇ⇒≡ _ _ (All.lookup (T-all _ (allFin kX) loops) (∈-allFin a))
          walk : ∀ u → ¬ IsTrue (AX.isFinal X′ (AX.run X′ p u))
          walk []      f = T-not⁻ nf f
          walk (a ∷ u) f = walk u (subst (λ r → IsTrue (AX.isFinal X′ (AX.run X′ r u))) (stay a) f)

      sinkY-dead : ∀ q u → IsTrue (sinkY q) → ¬ AccY q u
      sinkY-dead q u t with T-∧⁻ {Data.Bool.Base.not (AY.isFinal Y′ q)} t
      ... | nf , loops = walk u
        where
          stay : ∀ b → AY.next Y′ q b ≡ q
          stay b = ℕ.≡ᵇ⇒≡ _ _ (All.lookup (T-all _ (allFin kY) loops) (∈-allFin b))
          walk : ∀ u → ¬ IsTrue (AY.isFinal Y′ (AY.run Y′ q u))
          walk []      f = T-not⁻ nf f
          walk (b ∷ u) f = walk u (subst (λ r → IsTrue (AY.isFinal Y′ (AY.run Y′ r u))) (stay b) f)

      alive : ∀ {p q φ} → (p , q , φ) ∈ˡ univ → Reach (p , q , φ) → IsTrue (aliveᵇ (p , q , φ))
      alive {p} {q} {φ} m r with reach-sound r
      ... | u , u′ , f , g , _ =
        T-∧⁺ (T-not⁺ (λ t → sinkX-dead p u t f)) (T-not⁺ (λ t → sinkY-dead q u′ t g))

      reach→path : ∀ {s} → s ∈ˡ univ → Reach s → R.Reaches s
      reach→path m (stop f g) = _ , R.here , T-∧⁺ f g
      reach→path m (go {s′ = p , q , φ} mv r) with reach→path (step-univ m mv) r
      ... | c , pth , ac =
        c , R.there (∈-filter⁺ (λ s′ → T? (aliveᵇ s′)) (step-∈ᵐ mv) (alive (step-univ m mv) r)) pth , ac

      path→reach : ∀ {s c} → R.Path s c → IsTrue (accept c) → Reach s
      path→reach {c = p , q , zs} R.here ac with T-∧⁻ {AX.isFinal X′ p} ac
      ... | f , g = stop f g
      path→reach {c = _ , _ , zl _ _} R.here ()
      path→reach {c = _ , _ , zu _ _} R.here ()
      path→reach (R.there m pth) ac = go (∈-stepᵃ _ m) (path→reach pth ac)

    reach? : Dec (Reach start)
    reach? = map′ (λ t → let (c , pth , ac) = proj₁ (RC.found⇔ start-univ) t in path→reach pth ac)
                  (λ r → proj₂ (RC.found⇔ start-univ) (reach→path start-univ r))
                  (T? (R.found start))

  ----------------------------------------------------------------------
  -- A common run, decided

  open import Grades.Exact.Order T Op n code code-injective using () renaming (_⊑_ to _⊑ʷ_)
  open import Grades.Exact.Joint.Complete T Op n code code-injective running
    using (Common; sound-common; complete-common)

  open Moves X Y wfX wfY memo memo-faithful

  -- a walk on zones between words of the two expressions

  Zoned : Set
  Zoned = Σ[ v ∈ Word′ lower ] Σ[ w ∈ Word′ upper ] Wd L v × Wd U w × ZWalk v w zsync

  zoned? : Dec Zoned
  zoned? = map′ there′ back reach?
    where
      there′ : Reach start → Zoned
      there′ r with reach-sound r
      ... | u , u′ , f , g , j =
        map lX u , map lY u′ ,
        toRx⇒ L (C.code-sound rX (to (EX.elab-correct (codeRx rX) u) f)) ,
        toRx⇒ U (C.code-sound rY (to (EY.elab-correct (codeRx rY) u′) g)) , j

      back : Zoned → Reach start
      back (v , w , wv , ww , j) with C.code-complete rX (⇒toRx L wv) | C.code-complete rY (⇒toRx U ww)
      ... | u , cu , eu | u′ , cu′ , eu′ =
        reach-complete j (sym eu) (sym eu′) rs
          (from (EX.elab-correct (codeRx rX) u) cu) (from (EY.elab-correct (codeRx rY) u′) cu′)

  -- some exact word fits a word of each expression

  Consistentᵉ : Set
  Consistentᵉ = Σ[ x ∈ Word ] (Σ[ y ∈ Word ] ⟦ L ⟧ y × x ⊑ʷ y) × (Σ[ z ∈ Word ] ⟦ U ⟧ z × x ⊑ʷ z)

  consistentᵉ? : Dec Consistentᵉ
  consistentᵉ? = map′ to′ from′ zoned?
    where
      to′ : Zoned → Consistentᵉ
      to′ (v , w , wv , ww , j) with sound-common (zsound j)
      ... | x , (y , y∈ , fy) , (z , z∈ , fz) = x , (y , wd⇐ L wv y∈ , fy) , (z , wd⇐ U ww z∈ , fz)

      from′ : Consistentᵉ → Zoned
      from′ (x , (y , yL , fy) , (z , zU , fz)) with wd⇒ L yL | wd⇒ U zU
      ... | v , wv , y∈ | w , ww , z∈ =
        v , w , wv , ww , zcomplete (complete-common (x , (y , y∈ , fy) , (z , z∈ , fz)))

-- whether a lower and an upper expression have a common run

consistent? : (L : Expr lower) (U : Expr upper) → Dec (Search.Consistentᵉ L U)
consistent? L U = Search.consistentᵉ? L U
