------------------------------------------------------------------
-- Completeness checks, over an arbitrary specification.          --
--                                                                --
-- Inference checked against open derivations of pairs of         --
-- constructs. An entry is a derivation `∅ᴴ ∣ [] ⊢C⦂ C` of the    --
-- open calculus; its raw term is its erasure `⌊ D ⌋ᶜ`. A         --
-- `Verdict` states what `infer!` answers on that term: a type at --
-- least as good as `C`, a type worse than `C`, or a refusal.     --
--                                                                --
-- "At least as good" is open subtyping at the empty scope under  --
-- no hypotheses, `∅ᴴ ∣ Â ‼ ê <:̂ᶜ C`, decided by the grades' own  --
-- orders.                                                        --
--                                                                --
-- The handler entries take a clause family as a parameter; each  --
-- instance supplies forwarding, resuming and discarding ones.    --
--                                                                --
-- Entries, by the pair of constructs they combine:               --
--                                                                --
--          P    λ    I    S    D    B    U    H                  --
--     P    p-S  p-λ  p-I  p-S  p-D  p-B  p-U  h-P                --
--     λ         ·    λ-I  λ-S  λ-D  b-λ  u-λ  h-λ                --
--     I              ·    s-I  i-D  b-I  u-I  h-I, choose        --
--     S                   ·    s-D  b-S  b-S  h-S, h-keep        --
--     D                        ·    b-D  u-D  h-D                --
--     B                             b-g  b-U  h-B, h-box         --
--     U                                  ·    h-U, fwd-U         --
--     H                                       nest               --
--                                                                --
-- P perform, λ lam and application, I if, S sequencing, D delay, --
-- B box, U unbox, H handle; `h-ans` returns the handled answer.  --
------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; uncurry)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse; map′; _×-dec_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps     as H
import TypeInference.OpenSyntax.Types    as OT
import TypeInference.OpenSyntax.Contexts as OC
import TypeInference.OpenSyntax.Language as OL

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Demo.Completeness.Generic
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  -- an operation, and a value to pass it, for the entries that perform
  (op₀ : Operations.Op (LanguageSpec.Ops S))
  (arg₀ : ∀ {Θ n} {Q : H.Hyps S Θ} {Γ : OC.OCtx S Θ n}
        → OL._∣_⊢V⦂_ S Q Γ
            (OT.⌜_⌝ᵍ S (Operations.param (LanguageSpec.Ops S) op₀)))
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types    S using (_≡ᵇ?_)
open import Syntax.Contexts S using (Ctx; [])

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Language  S
open import TypeInference.OpenSyntax.Grounding S

open import TypeInference.OpenSyntax.ClosedContexts S using (skel)

open import TypeInference.Raw.Syntax S using (RawC)
open import TypeInference.Erase      S using (⌊_⌋ᶜ)
open import TypeInference.Infer S using (θ∅)

open import TypeInference.SolverImpl S opEnum umin?ᵣ umin?ₑ using (greportImpl)

------------------------------------------------------------------------
-- Open subtyping at the empty scope
--
-- A closed expression is convertible to the constant it denotes, so an
-- ordering between two of them is entailed exactly when their values
-- are ordered; grounding gives the converse.

private

  conv-e : (ε : EExp ∅ˢ) → ε ≡̂ₑ econst (⟦ ε ⟧ᵉ θ∅)
  conv-e (evar ())
  conv-e (econst _) = ≡̂ₑ-refl
  conv-e (ε ·̂ₑ ε')  = ≡̂ₑ-trans (≡̂ₑ-cong    (conv-e ε) (conv-e ε')) ≡̂ₑ-const-·
  conv-e (ε ⊔̂ₑ ε')  = ≡̂ₑ-trans (≡̂ₑ-cong-⊔ (conv-e ε) (conv-e ε')) ≡̂ₑ-const-⊔

  conv-r : (ρ : RExp ∅ˢ) → ρ ≡̂ᵣ rconst (⟦ ρ ⟧ʳ θ∅)
  conv-r (rvar ())
  conv-r (rconst _) = ≡̂ᵣ-refl
  conv-r (ρ ·̂ᵣ ρ')  = ≡̂ᵣ-trans (≡̂ᵣ-cong    (conv-r ρ) (conv-r ρ')) ≡̂ᵣ-const-·
  conv-r (ρ ⊔̂ᵣ ρ')  = ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (conv-r ρ) (conv-r ρ')) ≡̂ᵣ-const-⊔
  conv-r ∣ ε ∣̂ᵉ     = ≡̂ᵣ-trans (≡̂ᵣ-map-cong (conv-e ε)) ≡̂ᵣ-map-const

_≾̂ₑ?_ : (ε ε' : EExp ∅ˢ) → Dec (∅ᴴ ⊩ ε ≾̂ₑ ε')
ε ≾̂ₑ? ε' =
  map′ (λ p → transₑ (eqₑ (conv-e ε)) (transₑ (atomₑ p) (eqₑ (≡̂ₑ-sym (conv-e ε')))))
       (ground-≾ₑ {θ = θ∅} ∅ᴴ-⊨)
       (⟦ ε ⟧ᵉ θ∅ ≾ₑ? ⟦ ε' ⟧ᵉ θ∅)

_≾̂ᵣ?_ : (ρ ρ' : RExp ∅ˢ) → Dec (∅ᴴ ⊩ ρ ≾̂ᵣ ρ')
ρ ≾̂ᵣ? ρ' =
  map′ (λ p → transᵣ (eqᵣ (conv-r ρ)) (transᵣ (atomᵣ p) (eqᵣ (≡̂ᵣ-sym (conv-r ρ')))))
       (ground-≾ᵣ {θ = θ∅} ∅ᴴ-⊨)
       (⟦ ρ ⟧ʳ θ∅ ≾ᵣ? ⟦ ρ' ⟧ʳ θ∅)

infix 4 _<:̂ᵛ?_ _<:̂ᶜ?_

_<:̂ᵛ?_ : (A B : OVType ∅ˢ) → Dec (∅ᴴ ∣ A <:̂ᵛ B)
_<:̂ᶜ?_ : (C D : OCType ∅ˢ) → Dec (∅ᴴ ∣ C <:̂ᶜ D)

tvar ()   <:̂ᵛ? _
Base b    <:̂ᵛ? Base b'   = map′ Baseₛ (λ { (Baseₛ p) → p }) (b ≡ᵇ? b')
Base _    <:̂ᵛ? tvar ()
Base _    <:̂ᵛ? Unit      = no λ ()
Base _    <:̂ᵛ? Bool      = no λ ()
Base _    <:̂ᵛ? (_ |×| _) = no λ ()
Base _    <:̂ᵛ? Empty     = no λ ()
Base _    <:̂ᵛ? (_ ⇒ _)   = no λ ()
Base _    <:̂ᵛ? ([ _ ] _) = no λ ()
Unit      <:̂ᵛ? tvar ()
Unit      <:̂ᵛ? Base _    = no λ ()
Unit      <:̂ᵛ? Unit      = yes Unitₛ
Unit      <:̂ᵛ? Bool      = no λ ()
Unit      <:̂ᵛ? (_ |×| _) = no λ ()
Unit      <:̂ᵛ? Empty     = no λ ()
Unit      <:̂ᵛ? (_ ⇒ _)   = no λ ()
Unit      <:̂ᵛ? ([ _ ] _) = no λ ()
Bool      <:̂ᵛ? tvar ()
Bool      <:̂ᵛ? Base _    = no λ ()
Bool      <:̂ᵛ? Unit      = no λ ()
Bool      <:̂ᵛ? Bool      = yes Boolₛ
Bool      <:̂ᵛ? (_ |×| _) = no λ ()
Bool      <:̂ᵛ? Empty     = no λ ()
Bool      <:̂ᵛ? (_ ⇒ _)   = no λ ()
Bool      <:̂ᵛ? ([ _ ] _) = no λ ()
(_ |×| _) <:̂ᵛ? tvar ()
(_ |×| _) <:̂ᵛ? Base _    = no λ ()
(_ |×| _) <:̂ᵛ? Unit      = no λ ()
(_ |×| _) <:̂ᵛ? Bool      = no λ ()
(A |×| B) <:̂ᵛ? (A' |×| B') =
  map′ (uncurry _|×|ₛ_) (λ { (p |×|ₛ q) → p , q }) ((A <:̂ᵛ? A') ×-dec (B <:̂ᵛ? B'))
(_ |×| _) <:̂ᵛ? Empty     = no λ ()
(_ |×| _) <:̂ᵛ? (_ ⇒ _)   = no λ ()
(_ |×| _) <:̂ᵛ? ([ _ ] _) = no λ ()
Empty     <:̂ᵛ? tvar ()
Empty     <:̂ᵛ? Base _    = no λ ()
Empty     <:̂ᵛ? Unit      = no λ ()
Empty     <:̂ᵛ? Bool      = no λ ()
Empty     <:̂ᵛ? (_ |×| _) = no λ ()
Empty     <:̂ᵛ? Empty     = yes Emptyₛ
Empty     <:̂ᵛ? (_ ⇒ _)   = no λ ()
Empty     <:̂ᵛ? ([ _ ] _) = no λ ()
(_ ⇒ _)   <:̂ᵛ? tvar ()
(_ ⇒ _)   <:̂ᵛ? Base _    = no λ ()
(_ ⇒ _)   <:̂ᵛ? Unit      = no λ ()
(_ ⇒ _)   <:̂ᵛ? Bool      = no λ ()
(_ ⇒ _)   <:̂ᵛ? (_ |×| _) = no λ ()
(_ ⇒ _)   <:̂ᵛ? Empty     = no λ ()
(A ⇒ C)   <:̂ᵛ? (A' ⇒ C') =
  map′ (uncurry _⇒ₛ_) (λ { (p ⇒ₛ q) → p , q }) ((A' <:̂ᵛ? A) ×-dec (C <:̂ᶜ? C'))
(_ ⇒ _)   <:̂ᵛ? ([ _ ] _) = no λ ()
([ _ ] _) <:̂ᵛ? tvar ()
([ _ ] _) <:̂ᵛ? Base _    = no λ ()
([ _ ] _) <:̂ᵛ? Unit      = no λ ()
([ _ ] _) <:̂ᵛ? Bool      = no λ ()
([ _ ] _) <:̂ᵛ? (_ |×| _) = no λ ()
([ _ ] _) <:̂ᵛ? Empty     = no λ ()
([ _ ] _) <:̂ᵛ? (_ ⇒ _)   = no λ ()
([ ρ ] A) <:̂ᵛ? ([ ρ' ] A') =
  map′ (uncurry [_]ₛ_) (λ { ([ p ]ₛ q) → p , q }) ((ρ' ≾̂ᵣ? ρ) ×-dec (A <:̂ᵛ? A'))

(A ‼ ε) <:̂ᶜ? (A' ‼ ε') =
  map′ (uncurry _‼ₛ_) (λ { (p ‼ₛ q) → p , q }) ((A <:̂ᵛ? A') ×-dec (ε ≾̂ₑ? ε'))

-- the witness, or its refutation, read off the decision

≤! : ∀ {C D} → {{p : True (C <:̂ᶜ? D)}} → ∅ᴴ ∣ C <:̂ᶜ D
≤! {{p}} = toWitness p

≰! : ∀ {C D} → {{p : False (C <:̂ᶜ? D)}} → ¬ (∅ᴴ ∣ C <:̂ᶜ D)
≰! {{p}} = toWitnessFalse p

-- an entailed ordering between closed resource expressions, read off
-- the decision

⊩ᵣ! : ∀ {ρ ρ'} → {{p : True (ρ ≾̂ᵣ? ρ')}} → ∅ᴴ ⊩ ρ ≾̂ᵣ ρ'
⊩ᵣ! {{p}} = toWitness p

-- the variable at index `i` of a closed context, its lock grade decided
-- below the unit

#ᵛ : ∀ {n} {Γ : OCtx ∅ˢ n} → (i : Fin n) → {{p : True (lookup-gr Γ i ≾̂ᵣ? ûᵣ)}}
   → ∅ᴴ ∣ Γ ⊢V⦂ lookup-ty Γ i
#ᵛ i {{p}} = var (lookup-var _ i) (≾ᵘ-ok (toWitness p))

-- a grade ordering, read off the grade's own decision; the grades are
-- explicit, the orders unfolding to their components

≾ₑ! : (ε ε' : E) → {{p : True (ε ≾ₑ? ε')}} → ε ≾ₑ ε'
≾ₑ! _ _ {{p}} = toWitness p

≾ᵣ! : (ρ ρ' : R) → {{p : True (ρ ≾ᵣ? ρ')}} → ρ ≾ᵣ ρ'
≾ᵣ! _ _ {{p}} = toWitness p

------------------------------------------------------------------------
-- Verdicts

∅ᶜ : OCtx ∅ˢ 0
∅ᶜ = []

infer! : (Γ : Ctx) → RawC (skel Γ) → Maybe (OVType ∅ˢ × EExp ∅ˢ)
infer! = greportImpl

data Verdict {C : OCType ∅ˢ} (D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ C) : Set where

  -- inferred, at a type at least as good as `C`

  ok      : (Â : OVType ∅ˢ) → (ê : EExp ∅ˢ)
          → infer! [] ⌊ D ⌋ᶜ ≡ just (Â , ê)
          → ∅ᴴ ∣ Â ‼ ê <:̂ᶜ C
          → Verdict D

  -- inferred, at a type worse than `C`

  worse   : (Â : OVType ∅ˢ) → (ê : EExp ∅ˢ)
          → infer! [] ⌊ D ⌋ᶜ ≡ just (Â , ê)
          → ¬ (∅ᴴ ∣ Â ‼ ê <:̂ᶜ C)
          → Verdict D

  -- refused

  refused : infer! [] ⌊ D ⌋ᶜ ≡ nothing
          → Verdict D

------------------------------------------------------------------------
-- Building blocks

-- the operation's grade, and its result type

g₀ : E
g₀ = op-grade op₀

A₀ : ∀ {Θ} → OVType Θ
A₀ = ⌜ arity op₀ ⌝ᵍ

-- a variable used where no time has passed since it was bound

v : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
  → A ∈̂[ ûᵣ ] Γ → Q ∣ Γ ⊢V⦂ A
v x = var x (≾ᵘ-ok ⊩≾̂ᵣ-refl)

-- a variable of type `Unit`, used however late

v⋆ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ : RExp Θ}
   → Unit ∈̂[ ρ ] Γ → Q ∣ Γ ⊢V⦂ Unit
v⋆ x = var x (et-ok Unitₑ)

-- a variable of type `Bool`, used however late

v𝔹 : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ : RExp Θ}
   → Bool ∈̂[ ρ ] Γ → Q ∣ Γ ⊢V⦂ Bool
v𝔹 x = var x (et-ok Boolₑ)

-- `∣ uₑ ∣` is `uᵣ`, as a lock

map-û : ∀ {Θ} {Q : Hyps Θ} → Q ⊩ ûᵣ ·̂ᵣ ∣ ûₑ ∣̂ᵉ ≾̂ᵣ ûᵣ
map-û = transᵣ (eqᵣ (≡̂ᵣ-trans ≡̂ᵣ-identityˡ ≡̂ᵣ-map-const)) (atomᵣ (≾ᵣ-reflexive map-uᵉ))

------------------------------------------------------------------------
-- Handler clauses
--
-- A clause is typed at the rigid `evar newᵉ`, under the lock `⊤ᵣ`,
-- with the operation's parameter and its boxed continuation on top.

Clause : ∀ {Θ n} → Hyps Θ → OCtx Θ n → OVType Θ → Op → Set
Clause {Θ} Q Γ B op =
  wkᵉ-H Q ∣ wkᵉ-ctx Γ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
              ∷ [ rconst (mapᵉ (op-grade op)) ]
                  (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ}))
    ⊢C⦂ wkᵉ-v B ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ}))

-- a clause family at result type `Unit`, in any context

Clauses : Set
Clauses = ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → (op : Op) → Clause Q Γ Unit op

-- forwarding: perform the operation again, and resume with its answer

forward : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ} → (op : Op)
        → Clause Q Γ B op
forward {Θ} {B = B} op =
  perform op (v (Tl-∷ Hd))
    (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ)
      (<:̂ᵛ-refl (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ})))
      (v Hd · v (Tl-∷ Hd)))

-- resuming after idling `τ op`, with an answer of the arity type; the
-- idling has to fit the operation's grade, and to release the
-- continuation

resumeAfter : (τ : Op → ℕ)
            → ((op : Op) → of-natᵉ (τ op) ≾ₑ op-grade op)
            → ((op : Op) → of-natʳ (τ op) ≾ᵣ mapᵉ (op-grade op))
            → ((op : Op) → ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → Q ∣ Γ ⊢V⦂ ⌜ arity op ⌝ᵍ)
            → ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ} → (op : Op)
            → Clause Q Γ B op
resumeAfter τ τₑ τᵣ ans {Θ} {B = B} op =
  coerce (monoₑ (atomₑ (τₑ op)) ⊩≾̂ₑ-refl)
    (delay (τ op)
      (unbox (Tl-⟨⟩ Hd) (transᵣ (eqᵣ ≡̂ᵣ-identityˡ) (atomᵣ (τᵣ op)))
        (<:̂ᵛ-refl (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ})))
        (v Hd · ans op)))

-- resuming at once, which needs both units least

resumeNow : UnitMinᵣ → UnitMinₑ
          → ((op : Op) → ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → Q ∣ Γ ⊢V⦂ ⌜ arity op ⌝ᵍ)
          → ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ} → (op : Op)
          → Clause Q Γ B op
resumeNow minR minE ans {Θ} {B = B} op =
  unbox Hd (minᵣ minR)
    (<:̂ᵛ-refl (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ})))
    (coerce (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityˡ)) (monoₑ (minₑ minE) ⊩≾̂ₑ-refl))
      (v Hd · ans op))

-- resuming as `resumeAfter` does, with a `Bool` bound before the
-- resumption and returned after it

keepAfter : (τ : Op → ℕ)
          → ((op : Op) → of-natᵉ (τ op) ≾ₑ op-grade op)
          → ((op : Op) → of-natʳ (τ op) ≾ᵣ mapᵉ (op-grade op))
          → ((op : Op) → ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → Q ∣ Γ ⊢V⦂ ⌜ arity op ⌝ᵍ)
          → ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → (op : Op)
          → Clause Q Γ Bool op
keepAfter τ τₑ τᵣ ans {Θ} op =
  coerce (transₑ (eqₑ (≡̂ₑ-trans ≡̂ₑ-identityˡ (≡̂ₑ-cong ≡̂ₑ-refl ≡̂ₑ-identityʳ)))
                 (monoₑ (atomₑ (τₑ op)) ⊩≾̂ₑ-refl))
    (return false
     ⨟ delay (τ op)
         (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))
           (transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-cong (≡̂ᵣ-trans ≡̂ᵣ-identityˡ ≡̂ᵣ-map-const) ≡̂ᵣ-refl)
                                  ≡̂ᵣ-const-·))
                   (atomᵣ (≾ᵣ-trans (≾ᵣ-reflexive (trans (cong (_·ᵣ of-natʳ (τ op)) map-uᵉ)
                                                          (·ᵣ-identityˡ _)))
                                    (τᵣ op))))
           (<:̂ᵛ-refl (⌜ arity op ⌝ᵍ ⇒ Bool ‼ evar (newᵉ {Θ})))
           ((v Hd · ans op) ⨟ return (v𝔹 (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))))))

-- resuming at once, with a `Bool` bound before the resumption and
-- returned after it

keepNow : UnitMinᵣ → UnitMinₑ
        → ((op : Op) → ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → Q ∣ Γ ⊢V⦂ ⌜ arity op ⌝ᵍ)
        → ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → (op : Op)
        → Clause Q Γ Bool op
keepNow minR minE ans {Θ} op =
  coerce (transₑ (eqₑ (≡̂ₑ-trans ≡̂ₑ-identityˡ (≡̂ₑ-trans ≡̂ₑ-identityʳ (≡̂ₑ-sym ≡̂ₑ-identityˡ))))
                 (monoₑ (minₑ minE) ⊩≾̂ₑ-refl))
    (return false
     ⨟ unbox (Tl-∷ (Tl-⟨⟩ Hd))
         (transᵣ (eqᵣ (≡̂ᵣ-trans ≡̂ᵣ-identityˡ ≡̂ᵣ-map-const))
                 (transᵣ (atomᵣ (≾ᵣ-reflexive map-uᵉ)) (minᵣ minR)))
         (<:̂ᵛ-refl (⌜ arity op ⌝ᵍ ⇒ Bool ‼ evar (newᵉ {Θ})))
         ((v Hd · ans op) ⨟ return (v𝔹 (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))))))

-- discarding the continuation, which needs the effect unit least

discard : UnitMinₑ → Clauses
discard minE op = coerce (minₑ minE) (return ⋆)


-- H × I inside the clause: one family or the other, by a branch

choose : Clauses → Clauses → Clauses
choose H H' {Q = Q} {Γ = Γ} op =
  if true `then H {Q = Q} {Γ = Γ} op `else H' {Q = Q} {Γ = Γ} op

-- a clause family, at a given context

at : Clauses → ∀ {Θ n} → (Q : Hyps Θ) → (Γ : OCtx Θ n) → (op : Op) → Clause Q Γ Unit op
at H Q Γ op = H {Q = Q} {Γ = Γ} op

------------------------------------------------------------------------
-- Pairs without a handler

-- an arm's effect, joined with the other's

joinˡ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A ε ε'}
      → Q ∣ Γ ⊢C⦂ A ‼ ε → Q ∣ Γ ⊢C⦂ A ‼ (ε ⊔̂ₑ ε')
joinˡ = coerce ⊔-ubˡₑ

joinʳ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A ε ε'}
      → Q ∣ Γ ⊢C⦂ A ‼ ε' → Q ∣ Γ ⊢C⦂ A ‼ (ε ⊔̂ₑ ε')
joinʳ = coerce ⊔-ubʳₑ

-- one tick, and two

d₁ d₂ : ∀ {Θ} → EExp Θ
d₁ = econst (of-natᵉ 1)
d₂ = econst (of-natᵉ 2)

-- P × λ: a function that performs, applied

p-λ : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ A₀ ‼ (econst g₀ ·̂ₑ ûₑ)
p-λ = lam (perform op₀ arg₀ (return (v Hd))) · ⋆

-- P × I: one arm performs, the other returns

p-I : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (econst g₀ ·̂ₑ ûₑ ⊔̂ₑ ûₑ)
p-I = if true `then joinˡ (perform op₀ arg₀ (return ⋆)) `else joinʳ (return ⋆)

-- P × S: two operations in sequence

p-S : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ (econst g₀ ·̂ₑ ûₑ))
p-S = perform op₀ arg₀ (return (v Hd)) ⨟ perform op₀ arg₀ (return ⋆)

-- P × D: idling, then performing

p-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (d₁ ·̂ₑ (econst g₀ ·̂ₑ ûₑ))
p-D = delay 1 (perform op₀ arg₀ (return ⋆))

-- P × B: the answer boxed at the unit

p-B : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ [ ûᵣ ] A₀ ‼ (econst g₀ ·̂ₑ ûₑ)
p-B = perform op₀ arg₀
        (box ûᵣ (var (Tl-⟨⟩ Hd) (≾ᵘ-ok (eqᵣ ≡̂ᵣ-identityˡ))) (return (v Hd)))

-- P × U: a box of the operation's grade, opened after performing it

p-U : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (econst g₀ ·̂ₑ ûₑ)
p-U = box (rconst (mapᵉ g₀)) ⋆
        (perform op₀ arg₀
          (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl Unit) (return (v Hd))))

-- λ × I: a function branching on its argument

λ-I : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Bool ⇒ Unit ‼ (d₁ ·̂ₑ ûₑ ⊔̂ₑ ûₑ)) ‼ ûₑ
λ-I = return (lam (if v𝔹 Hd `then joinˡ (delay 1 (return ⋆)) `else joinʳ (return ⋆)))

-- λ × S: a function bound, then applied

λ-S : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (ûₑ ·̂ₑ (d₁ ·̂ₑ ûₑ))
λ-S = return (lam (delay 1 (return ⋆))) ⨟ (v Hd · ⋆)

-- λ × D: an argument used after idling

λ-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ (d₁ ·̂ₑ ûₑ)
λ-D = lam (delay 1 (return (v𝔹 (Tl-⟨⟩ Hd)))) · true

-- I × S: a branch, then an operation

s-I : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((d₁ ·̂ₑ ûₑ ⊔̂ₑ ûₑ) ·̂ₑ (econst g₀ ·̂ₑ ûₑ))
s-I = (if true `then joinˡ (delay 1 (return ⋆)) `else joinʳ (return ⋆))
      ⨟ perform op₀ arg₀ (return ⋆)

-- S × D: a value carried across two delays

s-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ ((d₁ ·̂ₑ ûₑ) ·̂ₑ (d₂ ·̂ₑ ûₑ))
s-D = delay 1 (return true) ⨟ delay 2 (return (v𝔹 (Tl-⟨⟩ Hd)))

-- I × D: arms idling for different times

i-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (d₁ ·̂ₑ ûₑ ⊔̂ₑ d₂ ·̂ₑ ûₑ)
i-D = if true `then joinˡ (delay 1 (return ⋆)) `else joinʳ (delay 2 (return ⋆))

-- B × λ: a function boxing its argument

b-λ : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Unit ⇒ [ ûᵣ ] Unit ‼ ûₑ) ‼ ûₑ
b-λ = return (lam (box ûᵣ (v⋆ (Tl-⟨⟩ Hd)) (return (v Hd))))

-- B alone, at the operation's grade: the box's grade is unannotated,
-- and nothing bounds it

b-g : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ [ rconst (mapᵉ g₀) ] Unit ‼ ûₑ
b-g = box (rconst (mapᵉ g₀)) ⋆ (return (v Hd))

-- U × λ: a function unboxing its argument, applied to a box

u-λ : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ûₑ
u-λ = box ûᵣ ⋆
        (lam (unbox Hd ⊩≾̂ᵣ-refl (<:̂ᵛ-refl Unit) (return (v Hd))) · v Hd)

-- B × I: both arms box

b-I : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ [ ûᵣ ] Unit ‼ ûₑ
b-I = if true `then box ûᵣ ⋆ (return (v Hd)) `else box ûᵣ ⋆ (return (v Hd))

-- U × I: one arm unboxes

u-I : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ûₑ
u-I = box ûᵣ ⋆
        (if true `then unbox Hd ⊩≾̂ᵣ-refl (<:̂ᵛ-refl Unit) (return (v Hd))
                 `else return ⋆)

-- B × S × U: a box returned, bound and opened

b-S : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (ûₑ ·̂ₑ ûₑ)
b-S = box ûᵣ ⋆ (return (v Hd))
      ⨟ unbox Hd ⊩≾̂ᵣ-refl (<:̂ᵛ-refl Unit) (return (v Hd))

-- B × D: boxing after idling

b-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ [ ûᵣ ] Unit ‼ (d₁ ·̂ₑ ûₑ)
b-D = delay 1 (box ûᵣ ⋆ (return (v Hd)))

-- U × D: a box of one tick, opened after idling for it

u-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (d₁ ·̂ₑ ûₑ)
u-D = box (rconst (of-natʳ 1)) ⋆
        (delay 1 (unbox (Tl-⟨⟩ Hd) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl Unit) (return (v Hd))))

-- B × U: a box opened at once

b-U : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ûₑ
b-U = box ûᵣ ⋆ (unbox Hd ⊩≾̂ᵣ-refl (<:̂ᵛ-refl Unit) (return (v Hd)))

------------------------------------------------------------------------
-- Pairs with a handler, for one clause family `H`

module Handling (H : Clauses) where

  -- H × P: the handled computation performs

  h-P : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-P = handle perform op₀ arg₀ (return ⋆) `with at H ∅ᴴ ∅ᶜ `in (return ⋆)

  -- H × S: it performs twice, in sequence

  h-S : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (((econst g₀ ·̂ₑ ûₑ) ·̂ₑ (econst g₀ ·̂ₑ ûₑ)) ·̂ₑ ûₑ)
  h-S = handle (perform op₀ arg₀ (return ⋆) ⨟ perform op₀ arg₀ (return ⋆))
        `with at H ∅ᴴ ∅ᶜ `in (return ⋆)

  -- H × λ: a function handling its argument's application

  h-λ : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ
  h-λ = return (lam (handle v Hd · ⋆
                     `with at H ∅ᴴ (∅ᶜ ∷ (Unit ⇒ Unit ‼ ûₑ)) `in (return ⋆)))

  -- H × I: the handled computation branches

  h-I : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst g₀ ·̂ₑ ûₑ ⊔̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-I = handle (if true `then joinˡ (perform op₀ arg₀ (return ⋆)) `else joinʳ (return ⋆))
        `with at H ∅ᴴ ∅ᶜ `in (return ⋆)

  -- H × D: the handled computation idles

  h-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((d₁ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-D = handle delay 1 (return ⋆) `with at H ∅ᴴ ∅ᶜ `in (return ⋆)

  -- H × B × U: a box of the operation's grade, opened by the
  -- continuation once the handled computation has performed

  h-B : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-B = box (rconst (mapᵉ g₀)) ⋆
          (handle perform op₀ arg₀ (return ⋆)
           `with at H ∅ᴴ (∅ᶜ ∷ [ rconst (mapᵉ g₀) ] Unit)
           `in (unbox (Tl-∷ (Tl-⟨⟩ Hd))
                  (eqᵣ (≡̂ᵣ-trans ≡̂ᵣ-identityˡ
                         (≡̂ᵣ-trans (≡̂ᵣ-map-cong ≡̂ₑ-identityʳ) ≡̂ᵣ-map-const)))
                  (<:̂ᵛ-refl Unit) (return (v Hd))))

  -- H × U: the same box, opened inside the handled computation

  h-U : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-U = box (rconst (mapᵉ g₀)) ⋆
          (handle perform op₀ arg₀
                    (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl Unit)
                      (return (v Hd)))
           `with at H ∅ᴴ (∅ᶜ ∷ [ rconst (mapᵉ g₀) ] Unit)
           `in (return ⋆))

-- H × S across the resumption: a clause family at result type `Bool`
-- that keeps a value bound before resuming

module Keeping (K : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → (op : Op) → Clause Q Γ Bool op)
  where

  h-keep : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-keep = handle perform op₀ arg₀ (return true)
           `with (λ op → K {Q = ∅ᴴ} {Γ = ∅ᶜ} op) `in (return (v Hd))

-- H × B, and a handler returning the operation's answer, for a family
-- at any result type

module Boxing (H : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ} → (op : Op)
                 → Clause Q Γ B op)
  where

  -- the continuation returns a box

  h-box : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ [ ûᵣ ] Unit ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-box = handle perform op₀ arg₀ (return ⋆)
          `with (λ op → H {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = [ ûᵣ ] Unit} op)
          `in (box ûᵣ ⋆ (return (v Hd)))

  -- the handled computation's answer is returned

  h-ans : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ A₀ ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-ans = handle perform op₀ arg₀ (return (v Hd))
          `with (λ op → H {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = A₀} op)
          `in (return (v Hd))

-- H × H': a handler inside another

module Nesting (H H' : Clauses) where

  nest : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  nest = handle (handle perform op₀ arg₀ (return ⋆) `with at H ∅ᴴ ∅ᶜ `in (return ⋆))
         `with at H' ∅ᴴ ∅ᶜ `in (return ⋆)

-- Hf × U: a forwarding clause that first opens a box from outside the
-- handler, across the clause's lock `⊤ᵣ`; the box is graded `⊤ᵣ`

fwd-U : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
fwd-U = box (rconst ⊤ᵣ) ⋆
          (handle perform op₀ arg₀ (return ⋆)
           `with (λ op →
             unbox (Tl-∷ (Tl-∷ (Tl-⟨⟩ Hd))) topᵣ (<:̂ᵛ-refl Unit)
               (perform op (v (Tl-∷ (Tl-∷ Hd)))
                 (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl _)
                   (v Hd · v (Tl-∷ Hd)))))
           `in (return ⋆))
