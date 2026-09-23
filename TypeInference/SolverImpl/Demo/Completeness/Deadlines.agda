--------------------------------------------------------------------------------
-- Completeness checks at deadlines.                                          --
--                                                                            --
-- Inference checked against open derivations of pairs of constructs, and     --
-- of `tempore-lang`'s example programs, at `Demo.TimeIntervals`'             --
-- deadlines: right-sided intervals as both grades, both units least.         --
--                                                                            --
--       P      Hf     Hr     Hd     B      U      λ      I      S      D     --
--   P   ok     ok     ok     ok     ok     ok     ok     ok     ok     ok    --
--   Hf         ok     ok     ok     ok     ok     ok     ok     ok     ok    --
--   Hr                ok     ok     ok     ok     ok     ok     ok/ref ok    --
--   Hd                       ok     ok     ok     ok     ok     ok     ok    --
--   B                               worse  ok     ok     ok     ok     ok    --
--   U                                      ·      ok     ok     ok     ok    --
--   λ                                             ·      ok     ok     ok    --
--   I                                                    ·      ok     ok    --
--   S                                                           ·      ok    --
--   D                                                                  ·     --
--                                                                            --
-- P perform; Hf, Hr, Hd handle with a forwarding, resuming or discarding     --
-- clause family; B box; U unbox; λ lam and application; I if; S              --
-- sequencing; D delay. `ok` inferred, at least as good as declared;          --
-- `ref` refused; `worse` inferred, worse than declared; `—` not              --
-- derivable; `·` no entry.                                                   --
--                                                                            --
-- Hr × S is refused where a value bound before the resumption is used        --
-- after it (`Kept`, `et-h`). B × B is `b-g`, a box whose grade nothing       --
-- bounds.                                                                    --
--------------------------------------------------------------------------------

open import Data.Maybe using (just; nothing)
open import Data.Fin using (zero; suc; #_)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read; write; send)
open import Syntax.Grades.Example.Worked.Spec using (reading)

open import TypeInference.Scopes

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ; opsᵈ₃; uᵈ-min; module Gᵐ)

import TypeInference.SolverImpl.Demo.Completeness.Generic

module TypeInference.SolverImpl.Demo.Completeness.Deadlines where

open LanguageSpec specᵈ
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades   specᵈ
open import TypeInference.OpenSyntax.Types    specᵈ
open import TypeInference.OpenSyntax.Contexts specᵈ
open import TypeInference.OpenSyntax.Hyps     specᵈ
open import TypeInference.OpenSyntax.Language specᵈ
open import TypeInference.OpenSyntax.Subst    specᵈ using (idˢ)
open import TypeInference.Constraints.Syntax  specᵈ using (Constraint; ∀ᵉ_; ∃ᵉ_; _∧̂_; _≾̂ₑᶜ_; Et∨≾ᵘ)
open import TypeInference.Constraints.Satisfaction specᵈ using (_⊨[_]_)

------------------------------------------------------------------------
-- Setup
--
-- Both units are least, so both options are taken; `read` takes `⋆`.

module M = TypeInference.SolverImpl.Demo.Completeness.Generic
             specᵈ opsᵈ₃ (just uᵈ-min) (just uᵈ-min) read ⋆

open M

-- an answer of each operation's arity type

ans : (op : Op) → ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → Q ∣ Γ ⊢V⦂ ⌜ arity op ⌝ᵍ
ans read  = const reading 0
ans write = ⋆
ans send  = ⋆

-- a resuming clause may idle a tick: it fits every operation's deadline

τ : Op → ℕ
τ _ = 1

τₑ : (op : Op) → of-natᵉ (τ op) ≾ₑ op-grade op
τₑ read  = ≾ₑ! (of-natᵉ 1) (op-grade read)
τₑ write = ≾ₑ! (of-natᵉ 1) (op-grade write)
τₑ send  = ≾ₑ! (of-natᵉ 1) (op-grade send)

τᵣ : (op : Op) → of-natʳ (τ op) ≾ᵣ mapᵉ (op-grade op)
τᵣ read  = ≾ᵣ! (of-natʳ 1) (mapᵉ (op-grade read))
τᵣ write = ≾ᵣ! (of-natʳ 1) (mapᵉ (op-grade write))
τᵣ send  = ≾ᵣ! (of-natʳ 1) (mapᵉ (op-grade send))

-- clause families: resuming at once, resuming after a tick, and
-- discarding

resume : Clauses
resume = resumeNow uᵈ-min uᵈ-min ans

resume₁ : Clauses
resume₁ = resumeAfter τ τₑ τᵣ ans

drop : Clauses
drop = discard uᵈ-min

module Hf = Handling forward
module Hr = Handling resume
module Hr₁ = Handling resume₁
module Hd = Handling drop

------------------------------------------------------------------------
-- Pairs without a handler

ex-p-λ : Verdict p-λ
ex-p-λ = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

ex-p-I : Verdict p-I
ex-p-I = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-p-S : Verdict p-S
ex-p-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

ex-p-D : Verdict p-D
ex-p-D = ok Unit (econst (of-natᵉ 2)) refl ≤!

ex-p-B : Verdict p-B
ex-p-B = ok ([ ûᵣ ] Base reading) (econst (of-natᵉ 1)) refl ≤!

ex-p-U : Verdict p-U
ex-p-U = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-λ-I : Verdict λ-I
ex-λ-I = ok (Bool ⇒ Unit ‼ econst (of-natᵉ 1)) ûₑ refl ≤!

ex-λ-S : Verdict λ-S
ex-λ-S = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-λ-D : Verdict λ-D
ex-λ-D = ok Bool (econst (of-natᵉ 1)) refl ≤!

ex-s-I : Verdict s-I
ex-s-I = ok Unit (econst (of-natᵉ 2)) refl ≤!

ex-s-D : Verdict s-D
ex-s-D = ok Bool (econst (of-natᵉ 3)) refl ≤!

ex-i-D : Verdict i-D
ex-i-D = ok Unit (econst (of-natᵉ 2)) refl ≤!

ex-b-λ : Verdict b-λ
ex-b-λ = ok (Unit ⇒ [ ûᵣ ] Unit ‼ ûₑ) ûₑ refl ≤!

ex-b-g : Verdict b-g
ex-b-g = worse ([ ûᵣ ] Unit) ûₑ refl ≰!

ex-u-λ : Verdict u-λ
ex-u-λ = ok Unit ûₑ refl ≤!

ex-b-I : Verdict b-I
ex-b-I = ok ([ ûᵣ ] Unit) ûₑ refl ≤!

ex-u-I : Verdict u-I
ex-u-I = ok Unit ûₑ refl ≤!

ex-b-S : Verdict b-S
ex-b-S = ok Unit ûₑ refl ≤!

ex-b-D : Verdict b-D
ex-b-D = ok ([ ûᵣ ] Unit) (econst (of-natᵉ 1)) refl ≤!

ex-u-D : Verdict u-D
ex-u-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-b-U : Verdict b-U
ex-b-U = ok Unit ûₑ refl ≤!

------------------------------------------------------------------------
-- Pairs with a handler

module Forwarding where

  open Hf

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (of-natᵉ 1)) refl ≤!

module Resuming where

  open Hr

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (of-natᵉ 1)) refl ≤!

module ResumingAfter where

  open Hr₁

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (of-natᵉ 1)) refl ≤!

module Discarding where

  open Hd

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-fwd-U : Verdict fwd-U
ex-fwd-U = ok Unit (econst (of-natᵉ 1)) refl ≤!

module Kept where

  module Now   = M.Keeping (keepNow uᵈ-min uᵈ-min ans)
  module After = M.Keeping (keepAfter τ τₑ τᵣ ans)

  ex-h-keep : Verdict Now.h-keep
  ex-h-keep = refused refl

  ex-h-keep-after : Verdict After.h-keep
  ex-h-keep-after = refused refl

module BoxedF where

  open M.Boxing (forward)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ ûᵣ ] Unit) (econst (of-natᵉ 1)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

module BoxedR where

  open M.Boxing (resumeNow uᵈ-min uᵈ-min ans)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ ûᵣ ] Unit) (econst (of-natᵉ 1)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

module BoxedR₁ where

  open M.Boxing (resumeAfter τ τₑ τᵣ ans)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ ûᵣ ] Unit) (econst (of-natᵉ 1)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

module Chosen where

  open M.Handling (choose forward drop)

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (of-natᵉ 1)) refl ≤!

module Nested where

  ex-fwd-in-fwd : Verdict (Nesting.nest forward forward)
  ex-fwd-in-fwd = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-fwd-in-res : Verdict (Nesting.nest forward resume)
  ex-fwd-in-res = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-fwd-in-drop : Verdict (Nesting.nest forward drop)
  ex-fwd-in-drop = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-res-in-fwd : Verdict (Nesting.nest resume forward)
  ex-res-in-fwd = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-res-in-res : Verdict (Nesting.nest resume resume)
  ex-res-in-res = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-res-in-drop : Verdict (Nesting.nest resume drop)
  ex-res-in-drop = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-drop-in-fwd : Verdict (Nesting.nest drop forward)
  ex-drop-in-fwd = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-drop-in-res : Verdict (Nesting.nest drop resume)
  ex-drop-in-res = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-drop-in-drop : Verdict (Nesting.nest drop drop)
  ex-drop-in-drop = ok Unit (econst (of-natᵉ 1)) refl ≤!

------------------------------------------------------------------------
-- Programs of `tempore-lang`'s examples
--
-- The prototype's `time-upper-bound` programs, read at these deadlines:
-- `Get` is `read`, `Tick` is `write`, integers are readings when an
-- operation's arity asks for one and `Bool` where they must be eternal,
-- and arithmetic keeps one operand.

d : ℕ → ∀ {Θ} → EExp Θ
d k = econst (of-natᵉ k)

-- `time_upper.tpe`, `foo1`: two delays spend the three ticks the box
-- allows

tu-foo1 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
tu-foo1 = box (rconst (of-natʳ 3)) (const reading 1)
            (delay 1 (return ⋆) ⨟ (delay 2 (return ⋆)
              ⨟ unbox (lookup-var _ (# 2)) ⊩ᵣ! (<:̂ᵛ-refl _) (return (v Hd))))

ex-tu-foo1 : Verdict tu-foo1
ex-tu-foo1 = ok (Base reading) (econst (of-natᵉ 3)) refl ≤!

-- `foo2`: two of the three ticks

tu-foo2 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
tu-foo2 = box (rconst (of-natʳ 3)) (const reading 1)
            (delay 2 (return ⋆)
              ⨟ unbox (lookup-var _ (# 1)) ⊩ᵣ! (<:̂ᵛ-refl _) (return (v Hd)))

ex-tu-foo2 : Verdict tu-foo2
ex-tu-foo2 = ok (Base reading) (econst (of-natᵉ 2)) refl ≤!

-- `handlers_upper_bound.tpe`, run on `let x = perform Get () in return x`

get : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ (econst (op-grade read) ·̂ₑ ûₑ)
get = perform read ⋆ (return (v Hd))

-- `h`: the clause idles the operation's tick and resumes

ub-h : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
ub-h = handle get
       `with (λ op → resumeAfter τ τₑ τᵣ ans {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = Base reading} op)
       `in (return (v Hd))

ex-ub-h : Verdict ub-h
ex-ub-h = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

-- `h_fast`: it idles less than the operation allows

ub-h-fast : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
ub-h-fast = handle get
            `with (λ op → resumeAfter (λ _ → 0)
                            (λ op → uᵈ-min (op-grade op)) (λ op → uᵈ-min (mapᵉ (op-grade op)))
                            ans {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = Base reading} op)
            `in (return (v Hd))

ex-ub-h-fast : Verdict ub-h-fast
ex-ub-h-fast = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

-- `h_abandon`: the clause never resumes

ub-h-abandon : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
ub-h-abandon = handle get
               `with (λ op → coerce (minₑ uᵈ-min) (return (const reading 0)))
               `in (return (v Hd))

ex-ub-h-abandon : Verdict ub-h-abandon
ex-ub-h-abandon = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

-- `h_before`: a local function is used before resuming, its result
-- kept across the resumption

ub-h-before : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
ub-h-before = handle get `with before `in (return (v Hd))
  where
    before : (op : Op) → Clause ∅ᴴ ∅ᶜ (Base reading) op
    before op =
      coerce (transₑ (eqₑ (≡̂ₑ-trans ≡̂ₑ-identityˡ (≡̂ₑ-trans ≡̂ₑ-identityˡ ≡̂ₑ-identityʳ)))
               (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityˡ)) (monoₑ (minₑ uᵈ-min) ⊩≾̂ₑ-refl)))
        (return (lam (return (const reading 1)))
         ⨟ ((v Hd · ⋆)
         ⨟ unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))
             (transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-cong (≡̂ᵣ-trans ≡̂ᵣ-identityˡ ≡̂ᵣ-map-const)
                                              ≡̂ᵣ-map-const)
                                    ≡̂ᵣ-const-·))
                     (minᵣ uᵈ-min))
             (<:̂ᵛ-refl _)
             ((v Hd · ans op) ⨟ return (v Hd))))

ex-ub-h-before : Verdict ub-h-before
ex-ub-h-before = ok (Base reading) (econst (of-natᵉ 1)) refl ≤!

-- `eternal_types.tpe`, `stamp_later`: an eternal value survives a wait

et-stamp : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ (ûₑ ·̂ₑ (d 3 ·̂ₑ ûₑ))
et-stamp = return true ⨟ delay 3 (return (v𝔹 (Tl-⟨⟩ Hd)))

ex-et-stamp : Verdict et-stamp
ex-et-stamp = ok Bool (econst (of-natᵉ 3)) refl ≤!

-- `keep 5`

et-keep : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ (d 1 ·̂ₑ ûₑ)
et-keep = lam (delay 1 (return (v𝔹 (Tl-⟨⟩ Hd)))) · true

ex-et-keep : Verdict et-keep
ex-et-keep = ok Bool (econst (of-natᵉ 1)) refl ≤!

-- `after (fun () -> delay 2) 5`: the kept value is eternal

after : ∀ {A : OVType ∅ˢ} {ε}
      → ∅ᴴ ∣ (∅ᶜ ∷ (Unit ⇒ Unit ‼ ε) ∷ A) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ Unit ⊢V⦂ A
      → ∅ᴴ ∣ ∅ᶜ ⊢V⦂ (Unit ⇒ Unit ‼ ε) ⇒ (A ⇒ A ‼ (ε ·̂ₑ ûₑ)) ‼ ûₑ
after x = lam (return (lam ((v (Tl-∷ Hd) · ⋆) ⨟ return x)))

et-after : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ (ûₑ ·̂ₑ ((d 2 ·̂ₑ ûₑ) ·̂ₑ ûₑ))
et-after = (after (v𝔹 (Tl-∷ (Tl-⟨⟩ Hd))) · lam (delay 2 (return ⋆)))
           ⨟ (v Hd · true)

ex-et-after : Verdict et-after
ex-et-after = ok Bool (econst (of-natᵉ 2)) refl ≤!

-- `after (fun () -> ()) (fun () -> ())`: `g` takes no time

et-after-pure : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Unit ⇒ Unit ‼ ûₑ) ‼ (ûₑ ·̂ₑ (ûₑ ·̂ₑ ûₑ))
et-after-pure = (after (var (Tl-∷ (Tl-⟨⟩ Hd)) (≾ᵘ-ok map-û)) · lam (return ⋆))
                ⨟ (v Hd · lam (return ⋆))

ex-et-after-pure : Verdict et-after-pure
ex-et-after-pure = ok (Unit ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

-- `handle (perform Tick (); 1) with h 2`: the `Tick` clause resumes and
-- returns the eternal value captured from outside the handler

et-h : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Bool ‼ _
et-h = return false
       ⨟ handle perform write (const reading 0) (return true)
         `with tick
         `in (return (v Hd))
  where
    tick : (op : Op) → Clause ∅ᴴ (∅ᶜ ⟨ ∣ ûₑ ∣̂ᵉ ⟩ ∷ Bool) Bool op
    tick write =
      coerce (transₑ (eqₑ ≡̂ₑ-identityʳ)
               (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityˡ)) (monoₑ (minₑ uᵈ-min) ⊩≾̂ₑ-refl)))
        (unbox Hd (minᵣ uᵈ-min) (<:̂ᵛ-refl _) (v Hd · ⋆)
         ⨟ return (v𝔹 (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ Hd)))))))
    tick read  = forward read
    tick send  = forward send

-- refused: `x` is used under the lock of the resumption, as in `Kept`

ex-et-h : Verdict et-h
ex-et-h = refused refl

------------------------------------------------------------------------
-- The refusals of `Kept` and `et-h`, as a constraint
--
-- A var-rule disjunction at `Bool` whose lock is an effect unknown
-- bounded below by a clause's rigid, as the lock `∣ ε ∣` left by a
-- resumption `k · a` is. It holds by eternality, and is declined.

keptC : Constraint ∅ˢ
keptC = ∀ᵉ (∃ᵉ ((evar (suc zero) ≾̂ₑᶜ evar zero) ∧̂ Et∨≾ᵘ Bool (∣ evar zero ∣̂ᵉ)))

keptC-sat : idˢ ⊨[ ∅ᴴ ] keptC
keptC-sat = evar zero , ⊩≾̂ₑ-refl , et-ok Boolₑ

keptC-declined : Gᵐ.solved? (Gᵐ.gsolveImpl keptC) ≡ nothing
keptC-declined = refl
