------------------------------------------------------------------
-- Tests, over an arbitrary specification.                        --
--                                                                --
-- Inference checked against open derivations of pairs of         --
-- constructs. A test is a derivation `Q ∣ Γ ⊢C⦂ C` of the open   --
-- calculus; its raw term is its erasure `⌊ D ⌋ᶜ`. Its `Outcome`  --
-- is what `reportOf` answers on that term in `Γ`: the principal  --
-- report, written out in full, or a refusal.                     --
--                                                                --
-- The handler tests take a clause family as a parameter; each    --
-- instance supplies forwarding, resuming and discarding ones.    --
--                                                                --
-- Each grade system's index module lists which test covers       --
-- which pair of constructs.                                      --
------------------------------------------------------------------

open import Data.Fin using (Fin)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ)

open import Relation.Nullary.Decidable using (True; toWitness)

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

module TypeInference.Tests.Generic
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  -- an operation, and a value to pass it, for the tests that perform
  (op₀ : Operations.Op (LanguageSpec.Ops S))
  (arg₀ : ∀ {Θ n} {Q : H.Hyps S Θ} {Γ : OC.OCtx S Θ n}
        → OL._∣_⊢V⦂_ S Q Γ
            (OT.⌜_⌝ᵍ S (Operations.param (LanguageSpec.Ops S) op₀)))
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Language  S
open import TypeInference.OpenSyntax.Grounding S using (Grounding; grounding; ⟦_⟧ᵉ; ⟦_⟧ʳ)

open import TypeInference.Erase S using (⌊_⌋ᶜ)

open import TypeInference.SolverImpl.Demo.Report S opEnum umin?ᵣ umin?ₑ
  using (Report; reportOf) public

------------------------------------------------------------------------
-- Closed grade orderings
--
-- A closed expression is convertible to the constant it denotes, so an
-- ordering between two of them is entailed when their values are
-- ordered.

private

  θ∅ : Grounding ∅ˢ
  θ∅ = grounding (λ ()) (λ ()) (λ ())

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

  closedᵣ : (ρ ρ' : RExp ∅ˢ) → ⟦ ρ ⟧ʳ θ∅ ≾ᵣ ⟦ ρ' ⟧ʳ θ∅ → ∅ᴴ ⊩ ρ ≾̂ᵣ ρ'
  closedᵣ ρ ρ' p = transᵣ (eqᵣ (conv-r ρ)) (transᵣ (atomᵣ p) (eqᵣ (≡̂ᵣ-sym (conv-r ρ'))))

-- an entailed ordering between closed resource expressions, read off
-- the grade's own decision

⊩ᵣ! : ∀ {ρ ρ'} → {{p : True (⟦ ρ ⟧ʳ θ∅ ≾ᵣ? ⟦ ρ' ⟧ʳ θ∅)}} → ∅ᴴ ⊩ ρ ≾̂ᵣ ρ'
⊩ᵣ! {ρ} {ρ'} {{p}} = closedᵣ ρ ρ' (toWitness p)

-- the variable at index `i` of a closed context, its lock grade decided
-- below the unit

#ᵛ : ∀ {n} {Γ : OCtx ∅ˢ n} → (i : Fin n)
   → {{p : True (⟦ lookup-gr Γ i ⟧ʳ θ∅ ≾ᵣ? uᵣ)}}
   → ∅ᴴ ∣ Γ ⊢V⦂ lookup-ty Γ i
#ᵛ {Γ = Γ} i {{p}} = var (lookup-var _ i) (≾ᵘ-ok (closedᵣ (lookup-gr Γ i) ûᵣ (toWitness p)))

-- a grade ordering, read off the grade's own decision; the grades are
-- explicit, the orders unfolding to their components

≾ₑ! : (ε ε' : E) → {{p : True (ε ≾ₑ? ε')}} → ε ≾ₑ ε'
≾ₑ! _ _ {{p}} = toWitness p

≾ᵣ! : (ρ ρ' : R) → {{p : True (ρ ≾ᵣ? ρ')}} → ρ ≾ᵣ ρ'
≾ᵣ! _ _ {{p}} = toWitness p

------------------------------------------------------------------------
-- Outcomes

∅ᶜ : OCtx ∅ˢ 0
∅ᶜ = []

data Outcome {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ} (D : Q ∣ Γ ⊢C⦂ C)
  : Set where

  -- reported, with principal report `R`

  ok      : (R : Report) → just R ≡ reportOf Γ ⌊ D ⌋ᶜ → Outcome D

  -- refused

  refused : nothing ≡ reportOf Γ ⌊ D ⌋ᶜ → Outcome D

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


-- handler × conditional inside the clause: one family or the other, by
-- a branch

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

-- perform × function: a function that performs, applied

p-λ : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ A₀ ‼ (econst g₀ ·̂ₑ ûₑ)
p-λ = lam (perform op₀ arg₀ (return (v Hd))) · ⋆

-- perform × conditional: one arm performs, the other returns

p-I : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (econst g₀ ·̂ₑ ûₑ ⊔̂ₑ ûₑ)
p-I = if true `then joinˡ (perform op₀ arg₀ (return ⋆)) `else joinʳ (return ⋆)

-- perform × sequencing: two operations in sequence

p-S : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ (econst g₀ ·̂ₑ ûₑ))
p-S = perform op₀ arg₀ (return (v Hd)) ⨟ perform op₀ arg₀ (return ⋆)

-- perform × delay: idling, then performing

p-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (d₁ ·̂ₑ (econst g₀ ·̂ₑ ûₑ))
p-D = delay 1 (perform op₀ arg₀ (return ⋆))

-- perform × box: the answer boxed at the unit

p-B : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ [ ûᵣ ] A₀ ‼ (econst g₀ ·̂ₑ ûₑ)
p-B = perform op₀ arg₀
        (box ûᵣ (var (Tl-⟨⟩ Hd) (≾ᵘ-ok (eqᵣ ≡̂ᵣ-identityˡ))) (return (v Hd)))

-- perform × unbox: a box of the operation's grade, opened after
-- performing it

p-U : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (econst g₀ ·̂ₑ ûₑ)
p-U = box (rconst (mapᵉ g₀)) ⋆
        (perform op₀ arg₀
          (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl Unit) (return (v Hd))))

-- function × conditional: a function branching on its argument

λ-I : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Bool ⇒ Unit ‼ (d₁ ·̂ₑ ûₑ ⊔̂ₑ ûₑ)) ‼ ûₑ
λ-I = return (lam (if v𝔹 Hd `then joinˡ (delay 1 (return ⋆)) `else joinʳ (return ⋆)))

-- function × sequencing: a function bound, then applied

λ-S : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (ûₑ ·̂ₑ (d₁ ·̂ₑ ûₑ))
λ-S = return (lam (delay 1 (return ⋆))) ⨟ (v Hd · ⋆)

-- function × delay: an argument used after idling

λ-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ (d₁ ·̂ₑ ûₑ)
λ-D = lam (delay 1 (return (v𝔹 (Tl-⟨⟩ Hd)))) · true

-- conditional × sequencing: a branch, then an operation

s-I : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((d₁ ·̂ₑ ûₑ ⊔̂ₑ ûₑ) ·̂ₑ (econst g₀ ·̂ₑ ûₑ))
s-I = (if true `then joinˡ (delay 1 (return ⋆)) `else joinʳ (return ⋆))
      ⨟ perform op₀ arg₀ (return ⋆)

-- sequencing × delay: a value carried across two delays

s-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ ((d₁ ·̂ₑ ûₑ) ·̂ₑ (d₂ ·̂ₑ ûₑ))
s-D = delay 1 (return true) ⨟ delay 2 (return (v𝔹 (Tl-⟨⟩ Hd)))

-- conditional × delay: arms idling for different times

i-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (d₁ ·̂ₑ ûₑ ⊔̂ₑ d₂ ·̂ₑ ûₑ)
i-D = if true `then joinˡ (delay 1 (return ⋆)) `else joinʳ (delay 2 (return ⋆))

-- box × function: a function boxing its argument

b-λ : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Unit ⇒ [ ûᵣ ] Unit ‼ ûₑ) ‼ ûₑ
b-λ = return (lam (box ûᵣ (v⋆ (Tl-⟨⟩ Hd)) (return (v Hd))))

-- B alone, at the operation's grade: the box's grade is unannotated,
-- and nothing bounds it

b-g : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ [ rconst (mapᵉ g₀) ] Unit ‼ ûₑ
b-g = box (rconst (mapᵉ g₀)) ⋆ (return (v Hd))

-- unbox × function: a function unboxing its argument, applied to a box

u-λ : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ûₑ
u-λ = box ûᵣ ⋆
        (lam (unbox Hd ⊩≾̂ᵣ-refl (<:̂ᵛ-refl Unit) (return (v Hd))) · v Hd)

-- box × conditional: both arms box

b-I : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ [ ûᵣ ] Unit ‼ ûₑ
b-I = if true `then box ûᵣ ⋆ (return (v Hd)) `else box ûᵣ ⋆ (return (v Hd))

-- unbox × conditional: one arm unboxes

u-I : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ûₑ
u-I = box ûᵣ ⋆
        (if true `then unbox Hd ⊩≾̂ᵣ-refl (<:̂ᵛ-refl Unit) (return (v Hd))
                 `else return ⋆)

-- box × sequencing × unbox: a box returned, bound and opened

b-S : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (ûₑ ·̂ₑ ûₑ)
b-S = box ûᵣ ⋆ (return (v Hd))
      ⨟ unbox Hd ⊩≾̂ᵣ-refl (<:̂ᵛ-refl Unit) (return (v Hd))

-- box × delay: boxing after idling

b-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ [ ûᵣ ] Unit ‼ (d₁ ·̂ₑ ûₑ)
b-D = delay 1 (box ûᵣ ⋆ (return (v Hd)))

-- unbox × delay: a box of one tick, opened after idling for it

u-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (d₁ ·̂ₑ ûₑ)
u-D = box (rconst (of-natʳ 1)) ⋆
        (delay 1 (unbox (Tl-⟨⟩ Hd) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl Unit) (return (v Hd))))

-- box × unbox: a box opened at once

b-U : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ûₑ
b-U = box ûᵣ ⋆ (unbox Hd ⊩≾̂ᵣ-refl (<:̂ᵛ-refl Unit) (return (v Hd)))

------------------------------------------------------------------------
-- Pairs with a handler, for one clause family `H`

module Handling (H : Clauses) where

  -- handler × perform: the handled computation performs

  h-P : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-P = handle perform op₀ arg₀ (return ⋆) `with at H ∅ᴴ ∅ᶜ `in (return ⋆)

  -- handler × sequencing: it performs twice, in sequence

  h-S : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (((econst g₀ ·̂ₑ ûₑ) ·̂ₑ (econst g₀ ·̂ₑ ûₑ)) ·̂ₑ ûₑ)
  h-S = handle (perform op₀ arg₀ (return ⋆) ⨟ perform op₀ arg₀ (return ⋆))
        `with at H ∅ᴴ ∅ᶜ `in (return ⋆)

  -- handler × function: a function handling its argument's application

  h-λ : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ (ûₑ ·̂ₑ ûₑ)) ‼ ûₑ
  h-λ = return (lam (handle v Hd · ⋆
                     `with at H ∅ᴴ (∅ᶜ ∷ (Unit ⇒ Unit ‼ ûₑ)) `in (return ⋆)))

  -- handler × conditional: the handled computation branches

  h-I : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst g₀ ·̂ₑ ûₑ ⊔̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-I = handle (if true `then joinˡ (perform op₀ arg₀ (return ⋆)) `else joinʳ (return ⋆))
        `with at H ∅ᴴ ∅ᶜ `in (return ⋆)

  -- handler × delay: the handled computation idles

  h-D : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((d₁ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-D = handle delay 1 (return ⋆) `with at H ∅ᴴ ∅ᶜ `in (return ⋆)

  -- handler × box × unbox: a box of the operation's grade, opened by the
  -- continuation once the handled computation has performed

  h-B : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-B = box (rconst (mapᵉ g₀)) ⋆
          (handle perform op₀ arg₀ (return ⋆)
           `with at H ∅ᴴ (∅ᶜ ∷ [ rconst (mapᵉ g₀) ] Unit)
           `in (unbox (Tl-∷ (Tl-⟨⟩ Hd))
                  (eqᵣ (≡̂ᵣ-trans ≡̂ᵣ-identityˡ
                         (≡̂ᵣ-trans (≡̂ᵣ-map-cong ≡̂ₑ-identityʳ) ≡̂ᵣ-map-const)))
                  (<:̂ᵛ-refl Unit) (return (v Hd))))

  -- handler × unbox: the same box, opened inside the handled computation

  h-U : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-U = box (rconst (mapᵉ g₀)) ⋆
          (handle perform op₀ arg₀
                    (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl Unit)
                      (return (v Hd)))
           `with at H ∅ᴴ (∅ᶜ ∷ [ rconst (mapᵉ g₀) ] Unit)
           `in (return ⋆))

-- handler × sequencing across the resumption: a clause family at
-- result type `Bool` that keeps a value bound before resuming

module Keeping (K : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → (op : Op) → Clause Q Γ Bool op)
  where

  h-keep : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  h-keep = handle perform op₀ arg₀ (return true)
           `with (λ op → K {Q = ∅ᴴ} {Γ = ∅ᶜ} op) `in (return (v Hd))

-- handler × box, and a handler returning the operation's answer, for a
-- family at any result type

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

-- handler × handler: a handler inside another

module Nesting (H H' : Clauses) where

  nest : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ (((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ) ·̂ₑ ûₑ)
  nest = handle (handle perform op₀ arg₀ (return ⋆) `with at H ∅ᴴ ∅ᶜ `in (return ⋆))
         `with at H' ∅ᴴ ∅ᶜ `in (return ⋆)

-- forwarding handler × unbox: a forwarding clause that first opens a
-- box from outside the handler, across the clause's lock `⊤ᵣ`; the box
-- is graded `⊤ᵣ`

fwd-U : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst g₀ ·̂ₑ ûₑ) ·̂ₑ ûₑ)
fwd-U = box (rconst ⊤ᵣ) ⋆
          (handle perform op₀ arg₀ (return ⋆)
           `with (λ op →
             unbox (Tl-∷ (Tl-∷ (Tl-⟨⟩ Hd))) topᵣ (<:̂ᵛ-refl Unit)
               (perform op (v (Tl-∷ (Tl-∷ Hd)))
                 (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl _)
                   (v Hd · v (Tl-∷ Hd)))))
           `in (return ⋆))
