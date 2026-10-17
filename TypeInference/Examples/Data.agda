--------------------------------------------------------------------
-- Inference on natural numbers                                   --
--                                                                --
-- Programs exercising `zero`, `succ` and `caseℕ`, and numerals   --
-- written with `numeral`. None has an annotation. `caseℕ V       --
-- `zero M `succ N` types both branches at one computation type,  --
-- `N` with the predecessor bound; `Nat` has no proper subtype    --
-- or supertype, and is eternal, so a natural number is usable    --
-- under any lock, where a function is not.                       --
--                                                                --
-- The durations are stepped: `⌜ n ⌝` is the duration of `n`      --
-- ticks, and `⌜ n ⌝ʳ` and `⌜ n ⌝ᵉ` its grades.                   --
--                                                                --
-- The instances under `Data/` check the verdicts and schemes by  --
-- `refl` at right- and left-sided time.                          --
--------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat using (ℕ; suc)

open import Relation.Nullary.Decidable using (True; toWitness)

open import Syntax.Durations using (Stepped)
open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.Examples.Data (S : LanguageSpec) (opEnum : OpEnum S)
  (st : Stepped (GradeSystem.Dur (LanguageSpec.Grades S))) where

open LanguageSpec S
open GradeSystemInterface Grades
  using (R; 𝔻; of-durʳ; of-durᵉ; uᵣ; _⊔ₑ_; _≾ᵣ?_)
  renaming (_≾ᵣ_ to _≾ᴳ_)

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Subst     S using (idˢ)
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S using (Satisfiable-∅)
open import TypeInference.OpenSyntax.Language  S
open import TypeInference.Raw.Syntax           S
open import TypeInference.Raw.Subst            S using (_[_]ᴿᶜ)
open import TypeInference.Erase                S using (⌊_⌋ᶜ)
open import TypeInference.Principality         S
open import TypeInference.SolverImpl           S opEnum
  using (infer-complete; infer-handlerFree)

open import TypeInference.SolverImpl S opEnum using (infer) public
open import TypeInference.Examples.Scheme S public
open import TypeInference.Examples.Variables

------------------------------------------------------------------
-- The duration of `n` ticks, and its grades

⌜_⌝ : ℕ → 𝔻
⌜ n ⌝ = Stepped.fromℕ st n

⌜_⌝ʳ : ∀ {Θ} → ℕ → RExp Θ
⌜ n ⌝ʳ = rconst (of-durʳ ⌜ n ⌝)

⌜_⌝ᵉ : ∀ {Θ} → ℕ → EExp Θ
⌜ n ⌝ᵉ = econst (of-durᵉ ⌜ n ⌝)

------------------------------------------------------------------
-- Verdicts

-- A closed derivation in the empty context is a typing

closed : {M : RawC ∅ˢ 0} {C : OCType ∅ˢ} → (D : ∅ᴴ ∣ [] ⊢C⦂ C)
       → ⌊ D ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ → Typable [] M
closed {C = C} D e = typable ∅ˢ idˢ ∅ᴴ C D e Satisfiable-∅

-- Typable and handler-free: inference answers `typed`

typed-of : (M : RawC ∅ˢ 0) → Typable [] M → HandlerFreeᶜ M → IsTyped (infer [] M)
typed-of M t h with infer [] M | infer-complete [] M t | infer-handlerFree [] M h
... | typed p   | _  | _  = is-typed p
... | untypable | nu | _  = ⊥-elim (nu refl)
... | stuck     | _  | ns = ⊥-elim (ns refl)

------------------------------------------------------------------
-- Side conditions

private

  -- A variable no time has passed over

  ok₀ : ∀ {Θ} {Q : Hyps Θ} {A : OVType Θ} → VarOK Q A ûᵣ
  ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

  -- A claim made after exactly the box's grade

  on-time : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → Q ⊩ ûᵣ ·̂ᵣ ρ ≾̂ᵣ ρ
  on-time = eqᵣ ≡̂ᵣ-identityˡ

  -- A use after a closed grade below the unit

  after : ∀ {Θ} {Q : Hyps Θ} {c : R} → c ≾ᴳ uᵣ → Q ⊩ ûᵣ ·̂ᵣ rconst c ≾̂ᵣ ûᵣ
  after p = transᵣ on-time (atomᵣ p)

------------------------------------------------------------------
-- 1. Eliminating a natural number
--
--   is-zero n = caseℕ n of zero ↦ true | succ m ↦ false
--   pred n    = caseℕ n of zero ↦ 0    | succ m ↦ m
--
-- The scrutinee is a `Nat`, and so is the predecessor. Typed at
-- every grade, with no type variable.

is-zero : RawC ∅ˢ 0
is-zero = return (lam (caseℕ v₀ `zero return true `succ return false))

is-zero-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat ⇒ Bool ‼ ûₑ) ‼ ûₑ
is-zero-D = return (lam (caseℕ var Hd ok₀ `zero return true `succ return false))

is-zero-typed : IsTyped (infer [] is-zero)
is-zero-typed = typed-of is-zero (closed is-zero-D refl) _

expected-is-zero : Scheme
expected-is-zero = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat ⇒ Bool ‼ ûₑ) ‼ ûₑ

pred : RawC ∅ˢ 0
pred = return (lam (caseℕ v₀ `zero return zero `succ return v₀))

pred-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat ⇒ Nat ‼ ûₑ) ‼ ûₑ
pred-D = return (lam (caseℕ var Hd ok₀ `zero return zero `succ return (var Hd ok₀)))

pred-typed : IsTyped (infer [] pred)
pred-typed = typed-of pred (closed pred-D refl) _

expected-pred : Scheme
expected-pred = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat ⇒ Nat ‼ ûₑ) ‼ ûₑ

-- The scrutinee has to be a natural number: `Bool` is not a subtype
-- of `Nat`.
--
--   case-of-bool = caseℕ true of zero ↦ () | succ m ↦ ()

case-of-bool : RawC ∅ˢ 0
case-of-bool = caseℕ true `zero return ⋆ `succ return ⋆

------------------------------------------------------------------
-- 2. A natural number used under a lock
--
--   later-succ n = delay 1; succ n
--
-- `n` is used under the lock `⟨ ⌜ 1 ⌝ʳ ⟩`; its type is `Nat`,
-- which is eternal, so `var` asks for nothing. Typed at every grade.

later-succ : RawC ∅ˢ 0
later-succ = return (lam (delay ⌜ 1 ⌝ (return (succ v₀))))

later-succ-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat ⇒ Nat ‼ (⌜ 1 ⌝ᵉ ·̂ₑ ûₑ)) ‼ ûₑ
later-succ-D = return (lam (delay ⌜ 1 ⌝ (return (succ (var (Tl-⟨⟩ Hd) (et-ok Natₑ))))))

later-succ-typed : IsTyped (infer [] later-succ)
later-succ-typed = typed-of later-succ (closed later-succ-D refl) _

expected-later-succ : Scheme
expected-later-succ = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat ⇒ Nat ‼ ⌜ 1 ⌝ᵉ) ‼ ûₑ

-- The same argument at an unknown type: the var-rule disjunction
-- `eternal α ∨ ⌜ 1 ⌝ʳ ≾ uᵣ` is decided on its grade, dropped at the
-- left-sided grades, left as `eternal α` at the right-sided ones.
--
--   later-id x = delay 1; x

later-id : RawC ∅ˢ 0
later-id = return (lam (delay ⌜ 1 ⌝ (return v₀)))

expected-later-id-eternal : Scheme
expected-later-id-eternal =
  ∀[ 1 , 0 , 0 ] eternal α₀ ⟹ (α₀ ⇒ α₀ ‼ ⌜ 1 ⌝ᵉ) ‼ ûₑ

expected-later-id : Scheme
expected-later-id = ∀[ 1 , 0 , 0 ] ⊤ ⟹ (α₀ ⇒ α₀ ‼ ⌜ 1 ⌝ᵉ) ‼ ûₑ

-- A numeral bound before a tick and used after it: typed at every
-- grade.
--
--   numeral-later = let n = 2 in delay 1; succ n

numeral-later : RawC ∅ˢ 0
numeral-later = return (numeral 2) ⨟ delay ⌜ 1 ⌝ (return (succ v₀))

numeral-later-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Nat ‼ (ûₑ ·̂ₑ (⌜ 1 ⌝ᵉ ·̂ₑ ûₑ))
numeral-later-D =
  return (numeralᵛ 2) ⨟ delay ⌜ 1 ⌝ (return (succ (var (Tl-⟨⟩ Hd) (et-ok Natₑ))))

numeral-later-typed : IsTyped (infer [] numeral-later)
numeral-later-typed = typed-of numeral-later (closed numeral-later-D refl) _

expected-numeral-later : Scheme
expected-numeral-later = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Nat ‼ ⌜ 1 ⌝ᵉ

-- A function bound before a tick and called after it: a function type
-- is never eternal, so `var` asks for `⌜ 1 ⌝ʳ ≾ uᵣ`, which holds at
-- the left-sided grades only.
--
--   function-later = let f = (λ _. ()) in delay 1; f ()

function-later : RawC ∅ˢ 0
function-later = return (lam (return ⋆)) ⨟ delay ⌜ 1 ⌝ (v₀ · ⋆)

function-later-D : of-durʳ ⌜ 1 ⌝ ≾ᴳ uᵣ → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Unit ‼ (ûₑ ·̂ₑ (⌜ 1 ⌝ᵉ ·̂ₑ ûₑ))
function-later-D q =
  return (lam {A = Unit} (return ⋆))
  ⨟ delay ⌜ 1 ⌝ (var (Tl-⟨⟩ Hd) (≾ᵘ-ok (after q)) · ⋆)

function-later-typable : True (of-durʳ ⌜ 1 ⌝ ≾ᵣ? uᵣ) → Typable [] function-later
function-later-typable q = closed (function-later-D (toWitness q)) refl

expected-function-later : Scheme
expected-function-later = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Unit ‼ ⌜ 1 ⌝ᵉ

------------------------------------------------------------------
-- 3. A boxed numeral
--
--   boxed-numeral = box[2] 3 as x in delay 2; unbox x as n in succ n
--
-- The claim is on time at every grade.

boxed-numeral : RawC ∅ˢ 0
boxed-numeral = box ⌜ 2 ⌝ʳ (numeral 3) (delay ⌜ 2 ⌝ (unbox fzero (return (succ v₀))))

boxed-numeral-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Nat ‼ (⌜ 2 ⌝ᵉ ·̂ₑ ûₑ)
boxed-numeral-D =
  box ⌜ 2 ⌝ʳ (numeralᵛ 3)
    (delay ⌜ 2 ⌝ (unbox (Tl-⟨⟩ Hd) on-time (<:̂ᵛ-refl _) (return (succ (var Hd ok₀)))))

boxed-numeral-typed : IsTyped (infer [] boxed-numeral)
boxed-numeral-typed = typed-of boxed-numeral (closed boxed-numeral-D refl) _

expected-boxed-numeral : Scheme
expected-boxed-numeral = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Nat ‼ ⌜ 2 ⌝ᵉ

------------------------------------------------------------------
-- 4. Branches of different effects
--
--   joined n = caseℕ n of zero ↦ delay 1; 0 | succ m ↦ delay 3; m
--
-- The effect is the join `⌜ 1 ⌝ ⊔ ⌜ 3 ⌝`: three ticks at the
-- right-sided grades, one at the left-sided ones. The predecessor is
-- used under the lock `⟨ ⌜ 3 ⌝ʳ ⟩`, which its type survives.

joined : RawC ∅ˢ 0
joined =
  return (lam (caseℕ v₀ `zero delay ⌜ 1 ⌝ (return zero)
                        `succ delay ⌜ 3 ⌝ (return v₀)))

joined-D : ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ (Nat ⇒ Nat ‼ (⌜ 1 ⌝ᵉ ⊔̂ₑ ⌜ 3 ⌝ᵉ)) ‼ ûₑ
joined-D =
  return (lam (caseℕ var Hd ok₀
    `zero coerce (transₑ (eqₑ ≡̂ₑ-identityʳ) ⊔-ubˡₑ) (delay ⌜ 1 ⌝ (return zero))
    `succ coerce (transₑ (eqₑ ≡̂ₑ-identityʳ) ⊔-ubʳₑ)
            (delay ⌜ 3 ⌝ (return (var (Tl-⟨⟩ Hd) (et-ok Natₑ))))))

joined-typed : IsTyped (infer [] joined)
joined-typed = typed-of joined (closed joined-D refl) _

expected-joined : Scheme
expected-joined =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹
    (Nat ⇒ Nat ‼ econst (of-durᵉ ⌜ 1 ⌝ ⊔ₑ of-durᵉ ⌜ 3 ⌝)) ‼ ûₑ
