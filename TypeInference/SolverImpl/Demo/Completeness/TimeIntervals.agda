--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows.                          --
--                                                                            --
-- Inference checked against open derivations of pairs of constructs, and     --
-- of `tempore-lang`'s example programs, at `Worked.Spec`: two-sided          --
-- windows as effect grades, lower bounds as resource grades.                 --
--                                                                            --
--       P      Hf     Hr     Hd     B      U      λ      I      S      D     --
--   P   ok     ok     ok     —      ok     ok     ok     ok     ok     ok    --
--   Hf         ok     ok     —      ok     ok     ok     ok     ok     ok    --
--   Hr                ok     —      ok     ok     ok     ok     ok     ok    --
--   Hd                       —      —      —      —      —      —      —     --
--   B                               ok     ok     ok     ok     ok     ok    --
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
--------------------------------------------------------------------------------

open import Data.Maybe using (nothing)
open import Data.Fin using (#_)
open import Data.Nat using (ℕ; z≤n; s≤s)
open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Util.Equality

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity using ([_,_,_]; ↑_)
open import Syntax.Grades.Example.Worked.Operations using (read; write; send)
open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.Scopes

open import TypeInference.SolverImpl.Demo.TimeIntervals using (ops₃)

import TypeInference.SolverImpl.Demo.Completeness.Generic

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals where

open LanguageSpec spec
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec
open import TypeInference.OpenSyntax.Hyps     spec
open import TypeInference.OpenSyntax.Language spec

------------------------------------------------------------------------
-- Setup
--
-- Neither unit is least here, so both options are declined; `read`
-- takes `⋆`.

module M = TypeInference.SolverImpl.Demo.Completeness.Generic spec ops₃ nothing nothing read ⋆

open M

-- an answer of each operation's arity type

ans : (op : Op) → ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → Q ∣ Γ ⊢V⦂ ⌜ arity op ⌝ᵍ
ans read  = const reading 0
ans write = ⋆
ans send  = ⋆

-- a resuming clause idles for the operation's shortest execution time

τ : Op → ℕ
τ read  = 1
τ write = 2
τ send  = 4

τₑ : (op : Op) → of-natᵉ (τ op) ≾ₑ op-grade op
τₑ read  = ≾ₑ! (of-natᵉ 1) (op-grade read)
τₑ write = ≾ₑ! (of-natᵉ 2) (op-grade write)
τₑ send  = ≾ₑ! (of-natᵉ 4) (op-grade send)

τᵣ : (op : Op) → of-natʳ (τ op) ≾ᵣ mapᵉ (op-grade op)
τᵣ read  = ≾ᵣ! (of-natʳ 1) (mapᵉ (op-grade read))
τᵣ write = ≾ᵣ! (of-natʳ 2) (mapᵉ (op-grade write))
τᵣ send  = ≾ᵣ! (of-natʳ 4) (mapᵉ (op-grade send))

resume : Clauses
resume = resumeAfter τ τₑ τᵣ ans

-- no discarding clause is derivable: the unit is below no operation's
-- window

module Hf = Handling forward
module Hr = Handling resume

------------------------------------------------------------------------
-- Pairs without a handler

ex-p-λ : Verdict p-λ
ex-p-λ = ok (Base reading) (econst (op-grade read)) refl ≤!

ex-p-I : Verdict p-I
ex-p-I = ok Unit (econst [ 0 , ↑ 1 , z≤n ]) refl ≤!

ex-p-S : Verdict p-S
ex-p-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

ex-p-D : Verdict p-D
ex-p-D = ok Unit (econst (of-natᵉ 2)) refl ≤!

ex-p-B : Verdict p-B
ex-p-B = ok ([ ûᵣ ] Base reading) (econst (op-grade read)) refl ≤!

ex-p-U : Verdict p-U
ex-p-U = ok Unit (econst (op-grade read)) refl ≤!

ex-λ-I : Verdict λ-I
ex-λ-I = ok (Bool ⇒ Unit ‼ econst [ 0 , ↑ 1 , z≤n ]) ûₑ refl ≤!

ex-λ-S : Verdict λ-S
ex-λ-S = ok Unit (econst (of-natᵉ 1)) refl ≤!

ex-λ-D : Verdict λ-D
ex-λ-D = ok Bool (econst (of-natᵉ 1)) refl ≤!

ex-s-I : Verdict s-I
ex-s-I = ok Unit (econst [ 1 , ↑ 2 , s≤s z≤n ]) refl ≤!

ex-s-D : Verdict s-D
ex-s-D = ok Bool (econst (of-natᵉ 3)) refl ≤!

ex-i-D : Verdict i-D
ex-i-D = ok Unit (econst [ 1 , ↑ 2 , s≤s z≤n ]) refl ≤!

ex-b-λ : Verdict b-λ
ex-b-λ = ok (Unit ⇒ [ ûᵣ ] Unit ‼ ûₑ) ûₑ refl ≤!

ex-b-g : Verdict b-g
ex-b-g = ok ([ ûᵣ ] Unit) ûₑ refl ≤!

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
  ex-h-P = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst [ 0 , ↑ 1 , z≤n ]) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (op-grade read)) refl ≤!

  ex-fwd-U : Verdict fwd-U
  ex-fwd-U = ok Unit (econst (op-grade read)) refl ≤!

module Resuming where

  open Hr

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-S : Verdict h-S
  ex-h-S = ok Unit (econst (of-natᵉ 2)) refl ≤!

  ex-h-λ : Verdict h-λ
  ex-h-λ = ok ((Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ûₑ refl ≤!

  ex-h-I : Verdict h-I
  ex-h-I = ok Unit (econst [ 0 , ↑ 1 , z≤n ]) refl ≤!

  ex-h-D : Verdict h-D
  ex-h-D = ok Unit (econst (of-natᵉ 1)) refl ≤!

  ex-h-B : Verdict h-B
  ex-h-B = ok Unit (econst (op-grade read)) refl ≤!

  ex-h-U : Verdict h-U
  ex-h-U = ok Unit (econst (op-grade read)) refl ≤!

module Kept where

  open M.Keeping (keepAfter τ τₑ τᵣ ans)

  ex-h-keep : Verdict h-keep
  ex-h-keep = ok Bool (econst (op-grade read)) refl ≤!

module BoxedF where

  open M.Boxing (forward)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ ûᵣ ] Unit) (econst (op-grade read)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (op-grade read)) refl ≤!

module BoxedR where

  open M.Boxing (resumeAfter τ τₑ τᵣ ans)

  ex-h-box : Verdict h-box
  ex-h-box = ok ([ ûᵣ ] Unit) (econst (op-grade read)) refl ≤!

  ex-h-ans : Verdict h-ans
  ex-h-ans = ok (Base reading) (econst (op-grade read)) refl ≤!

module Chosen where

  open M.Handling (choose forward resume)

  ex-h-P : Verdict h-P
  ex-h-P = ok Unit (econst (op-grade read)) refl ≤!

module Nested where

  module FF = Nesting forward forward
  module FR = Nesting forward resume
  module RF = Nesting resume forward
  module RR = Nesting resume resume

  ex-fwd-in-fwd : Verdict FF.nest
  ex-fwd-in-fwd = ok Unit (econst (op-grade read)) refl ≤!

  ex-fwd-in-res : Verdict FR.nest
  ex-fwd-in-res = ok Unit (econst (op-grade read)) refl ≤!

  ex-res-in-fwd : Verdict RF.nest
  ex-res-in-fwd = ok Unit (econst (op-grade read)) refl ≤!

  ex-res-in-res : Verdict RR.nest
  ex-res-in-res = ok Unit (econst (op-grade read)) refl ≤!

------------------------------------------------------------------------
-- Clause families choosing per operation

-- `read` resumes after idling its tick, the others are forwarded

readResumes : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ} → (op : Op)
            → Clause Q Γ B op
readResumes read  = resumeAfter τ τₑ τᵣ ans read
readResumes write = forward write
readResumes send  = forward send

-- `read` performs itself and resumes with a constant, the others are
-- forwarded

readPerforms : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ} → (op : Op)
             → Clause Q Γ B op
readPerforms {Θ} {B = B} read =
  perform read (v (Tl-∷ Hd))
    (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ)
      (<:̂ᵛ-refl (Base reading ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ})))
      (v Hd · const reading 42))
readPerforms write = forward write
readPerforms send  = forward send

-- `read` resumes with a reading bound outside the handler, which crosses
-- the clause's lock: `⊤ᵣ` is the resource unit here

readOffset : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ} → (op : Op)
           → Clause Q (Γ ∷ Base reading) B op
readOffset {Θ} {B = B} read =
  coerce (monoₑ (atomₑ (τₑ read)) ⊩≾̂ₑ-refl)
    (delay 1
      (unbox (Tl-⟨⟩ Hd) (transᵣ (eqᵣ ≡̂ᵣ-identityˡ) (atomᵣ (τᵣ read)))
        (<:̂ᵛ-refl (Base reading ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ})))
        (v Hd · var (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-∷ (Tl-⟨⟩ Hd))))) (≾ᵘ-ok topᵣ))))
readOffset write = forward write
readOffset send  = forward send

-- `write` resumes after idling, the others are forwarded

writeResumes : Clauses
writeResumes read  = forward read
writeResumes write = resumeAfter τ τₑ τᵣ ans write
writeResumes send  = forward send

-- `write` runs a handler of its own around a second `write`, then
-- resumes; the others are forwarded

writeNests : Clauses
writeNests read  = forward read
writeNests send  = forward send
writeNests {Θ} {Q = Q} {Γ = Γ} write =
  coerce (eqₑ (≡̂ₑ-cong ≡̂ₑ-identityʳ ≡̂ₑ-refl))
    (handle perform write (v (Tl-∷ Hd)) (return ⋆)
     `with at writeResumes _ _
     `in (unbox (Tl-∷ (Tl-⟨⟩ Hd))
            (eqᵣ (≡̂ᵣ-trans ≡̂ᵣ-identityˡ
                   (≡̂ᵣ-trans (≡̂ᵣ-map-cong ≡̂ₑ-identityʳ) ≡̂ᵣ-map-const)))
            (<:̂ᵛ-refl (Unit ⇒ Unit ‼ evar (newᵉ {Θ})))
            (v Hd · ⋆)))

-- H × H inside a clause: `write` handled by a clause that itself handles

h-in-clause : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ((econst (op-grade write) ·̂ₑ ûₑ) ·̂ₑ ûₑ)
h-in-clause = handle perform write (const reading 0) (return ⋆)
              `with at writeNests ∅ᴴ ∅ᶜ `in (return ⋆)

ex-h-in-clause : Verdict h-in-clause
ex-h-in-clause = ok Unit (econst (op-grade write)) refl ≤!

------------------------------------------------------------------------
-- Programs of `tempore-lang`'s examples
--
-- The prototype's `time-lower-bound` and `time-interval` programs, read
-- at these windows and lower bounds: `Get` is `read` and `Set` is
-- `write`, integers are readings, a resource window `(n, m)` is its
-- lower bound `[ n ,+∞⟩`, arithmetic is a pair of the operands, and a
-- two-constructor datatype is `Bool`.

d : ℕ → ∀ {Θ} → EExp Θ
d k = econst (of-natᵉ k)

-- `operations.tpe`, `foo`

ops-foo : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
ops-foo = perform read ⋆
            (perform write (const reading 42)
              (perform read ⋆ (return ⦉ v Hd , v Hd ⦊)))

ex-ops-foo : Verdict ops-foo
ex-ops-foo = ok (Base reading |×| Base reading) (econst [ 4 , ↑ 5 , s≤s (s≤s (s≤s (s≤s z≤n))) ]) refl ≤!

-- `delay.tpe`, `foo_int_temporal`, applied to `Zero`

fit : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n}
    → Q ∣ Γ ⊢V⦂ Bool ⇒ Base reading ‼ (d 3 ·̂ₑ ûₑ)
fit = lam (if v𝔹 Hd `then delay 3 (return (const reading 0))
                    `else delay 3 (return (const reading 1)))

dl-foo-int : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ (d 3 ·̂ₑ ûₑ)
dl-foo-int = fit · true

ex-dl-foo-int : Verdict dl-foo-int
ex-dl-foo-int = ok (Base reading) (econst (of-natᵉ 3)) refl ≤!

-- `del Zero`: the argument is computed in two ticks

dl-del : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ (d 9 ·̂ₑ ((d 2 ·̂ₑ ûₑ) ·̂ₑ (d 3 ·̂ₑ ûₑ)))
dl-del = delay 9 (delay 2 (return true) ⨟ (fit · v Hd))

ex-dl-del : Verdict dl-del
ex-dl-del = ok (Base reading) (econst (of-natᵉ 14)) refl ≤!

-- `higher 5 6`: the function's five ticks sit on the inner arrow

dl-higher : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ (ûₑ ·̂ₑ (d 5 ·̂ₑ ûₑ))
dl-higher = (lam (return (lam (delay 5 (return ⦉ #ᵛ (# 1) , #ᵛ (# 0) ⦊))))
               · const reading 5)
            ⨟ (#ᵛ (# 0) · const reading 6)

ex-dl-higher : Verdict dl-higher
ex-dl-higher = ok (Base reading |×| Base reading) (econst (of-natᵉ 5)) refl ≤!

-- `higher2 5 6`: ten ticks before the closure, five on it

dl-higher2 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading)
                          ‼ ((d 10 ·̂ₑ ûₑ) ·̂ₑ (d 5 ·̂ₑ ûₑ))
dl-higher2 = (lam (delay 10 (return (lam (delay 5 (return ⦉ #ᵛ (# 1) , #ᵛ (# 0) ⦊)))))
                · const reading 5)
             ⨟ (#ᵛ (# 0) · const reading 6)

ex-dl-higher2 : Verdict dl-higher2
ex-dl-higher2 = ok (Base reading |×| Base reading) (econst (of-natᵉ 15)) refl ≤!

-- `foobar ()`: `foo` instantiated at two delaying functions

F : ℕ → ∀ {Θ} → OVType Θ
F k = Base reading ⇒ Unit ‼ (d k ·̂ₑ ûₑ)

dl-foobar : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ _
dl-foobar =
  (foo · lam (delay 24 (return ⋆)))
  ⨟ ((#ᵛ (# 0) · lam (delay 23 (return ⋆))) ⨟ (#ᵛ (# 0) · const reading 7))
  where
    foo : ∅ᴴ ∣ ∅ᶜ ⊢V⦂ F 24 ⇒ (F 23 ⇒ (Base reading ⇒ Unit ‼
                          ((d 24 ·̂ₑ ûₑ) ·̂ₑ ((d 23 ·̂ₑ ûₑ) ·̂ₑ (d 42 ·̂ₑ ûₑ)))) ‼ ûₑ) ‼ ûₑ
    foo = lam (return (lam (return (lam
            ((#ᵛ (# 2) · #ᵛ (# 0))
              ⨟ ((#ᵛ (# 2) · #ᵛ (# 1)) ⨟ delay 42 (return ⋆)))))))

ex-dl-foobar : Verdict dl-foobar
ex-dl-foobar = ok Unit (econst (of-natᵉ 89)) refl ≤!

-- `test2 ()`: the delay banks the three ticks the box demands

dl-test2 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ (d 3 ·̂ₑ ûₑ)
dl-test2 = box (rconst (of-natʳ 3)) (const reading 42)
             (delay 3 (unbox (lookup-var _ (# 0)) ⊩ᵣ! (<:̂ᵛ-refl _) (return (v Hd))))

ex-dl-test2 : Verdict dl-test2
ex-dl-test2 = ok (Base reading) (econst (of-natᵉ 3)) refl ≤!

-- `time_intervals.tpe`, `foo1` to `foo5`: two delays, of three ticks
-- in all, then a box demanding one tick opened

ti-foo1 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
ti-foo1 = box (rconst (of-natʳ 1)) (const reading 1)
            (delay 1 (return ⋆) ⨟ (delay 2 (return ⋆)
              ⨟ unbox (lookup-var _ (# 2)) ⊩ᵣ! (<:̂ᵛ-refl _) (return (const reading 1))))

ex-ti-foo1 : Verdict ti-foo1
ex-ti-foo1 = ok (Base reading) (econst (of-natᵉ 3)) refl ≤!

ti-foo2 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Base reading ‼ _
ti-foo2 = box (rconst (of-natʳ 1)) (const reading 1)
            (delay 1 (return ⋆) ⨟ (delay 2 (return ⋆)
              ⨟ unbox (lookup-var _ (# 2)) ⊩ᵣ! (<:̂ᵛ-refl _) (return (v Hd))))

ex-ti-foo2 : Verdict ti-foo2
ex-ti-foo2 = ok (Base reading) (econst (of-natᵉ 3)) refl ≤!

ti-foo3 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
ti-foo3 = return (const reading 7)
          ⨟ box (rconst (of-natʳ 1)) (const reading 1)
              (delay 1 (return ⋆) ⨟ (delay 2 (return ⋆) ⨟ (return (const reading 3)
                ⨟ unbox (lookup-var _ (# 3)) ⊩ᵣ! (<:̂ᵛ-refl _)
                    (return ⦉ #ᵛ (# 0) , #ᵛ (# 1) ⦊))))

ex-ti-foo3 : Verdict ti-foo3
ex-ti-foo3 = ok (Base reading |×| Base reading) (econst (of-natᵉ 3)) refl ≤!

-- `x` is used three ticks after it is bound

ti-foo4 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
ti-foo4 = return (const reading 7)
          ⨟ box (rconst (of-natʳ 1)) (const reading 1)
              (delay 1 (return ⋆) ⨟ (delay 2 (return ⋆) ⨟ (return (const reading 3)
                ⨟ unbox (lookup-var _ (# 3)) ⊩ᵣ! (<:̂ᵛ-refl _)
                    (return ⦉ #ᵛ (# 0) , #ᵛ (# 5) ⦊))))

ex-ti-foo4 : Verdict ti-foo4
ex-ti-foo4 = ok (Base reading |×| Base reading) (econst (of-natᵉ 3)) refl ≤!

-- `x` boxed at two ticks as well, and both boxes opened

ti-foo5 : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| (Base reading |×| Base reading)) ‼ _
ti-foo5 = return (const reading 7)
          ⨟ box (rconst (of-natʳ 2)) (#ᵛ (# 0))
              (box (rconst (of-natʳ 1)) (const reading 1)
                (delay 1 (return ⋆) ⨟ (delay 2 (return ⋆) ⨟ (return (const reading 3)
                  ⨟ unbox (lookup-var _ (# 3)) ⊩ᵣ! (<:̂ᵛ-refl _)
                      (unbox (lookup-var _ (# 5)) ⊩ᵣ! (<:̂ᵛ-refl _)
                        (return ⦉ #ᵛ (# 1) , ⦉ #ᵛ (# 7) , #ᵛ (# 0) ⦊ ⦊))))))

ex-ti-foo5 : Verdict ti-foo5
ex-ti-foo5 = ok (Base reading |×| (Base reading |×| Base reading)) (econst (of-natᵉ 3)) refl ≤!

-- `3dprint.tpe`, the first run: two prints of seven ticks, each boxed
-- for five, then cured in five; a model is a `Bool`

print-model : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n}
            → Q ∣ Γ ⊢V⦂ Bool ⇒ [ rconst (of-natʳ 5) ] Bool ‼ (d 7 ·̂ₑ ûₑ)
print-model = lam (delay 7 (box (rconst (of-natʳ 5)) (v𝔹 (Tl-⟨⟩ (Tl-⟨⟩ Hd))) (return (v Hd))))

uv-cure : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n}
        → Q ∣ Γ ⊢V⦂ Bool ⇒ Bool ‼ (d 5 ·̂ₑ ûₑ)
uv-cure = lam (delay 5 (return (v𝔹 (Tl-⟨⟩ Hd))))

pr-run : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Bool |×| Bool) ‼ _
pr-run =
  return print-model ⨟ (return uv-cure
  ⨟ ((#ᵛ (# 1) · true)
  ⨟ ((#ᵛ (# 2) · false)
  ⨟ unbox (lookup-var _ (# 1)) ⊩ᵣ! (<:̂ᵛ-refl _)
      ((#ᵛ (# 3) · #ᵛ (# 0))
      ⨟ unbox (lookup-var _ (# 2)) ⊩ᵣ! (<:̂ᵛ-refl _)
          ((#ᵛ (# 5) · #ᵛ (# 0))
          ⨟ return ⦉ #ᵛ (# 1) , #ᵛ (# 0) ⦊)))))

ex-pr-run : Verdict pr-run
ex-pr-run = ok (Bool |×| Bool) (econst (of-natᵉ 24)) refl ≤!

-- `handlers_lower_bound.tpe`, `h`: `Get` resumes after its tick, `Set`
-- is forwarded, and the return case performs both

lb-h : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
lb-h = handle perform read ⋆ (return (v Hd))
       `with (λ op → readResumes {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = Base reading |×| Base reading} op)
       `in (perform write (const reading 42)
              (perform read ⋆ (return ⦉ #ᵛ (# 2) , #ᵛ (# 0) ⦊)))

ex-lb-h : Verdict lb-h
ex-lb-h = ok (Base reading |×| Base reading) (econst [ 4 , ↑ 5 , s≤s (s≤s (s≤s (s≤s z≤n))) ]) refl ≤!

-- `h'`: the same clauses, a return case that takes no time

lb-h' : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
lb-h' = handle perform read ⋆ (return (v Hd))
        `with (λ op → readResumes {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = Base reading |×| Base reading} op)
        `in (return ⦉ v Hd , v Hd ⦊)

ex-lb-h' : Verdict lb-h'
ex-lb-h' = ok (Base reading |×| Base reading) (econst (op-grade read)) refl ≤!

-- `h''`: the `Get` clause performs `Get` itself

lb-h'' : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
lb-h'' = handle perform read ⋆ (return (v Hd))
         `with (λ op → readPerforms {Q = ∅ᴴ} {Γ = ∅ᶜ} {B = Base reading |×| Base reading} op)
         `in (return ⦉ v Hd , v Hd ⦊)

ex-lb-h'' : Verdict lb-h''
ex-lb-h'' = ok (Base reading |×| Base reading) (econst (op-grade read)) refl ≤!

-- `h_offset 10`: the clause resumes with a reading bound outside it

lb-offset : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ (Base reading |×| Base reading) ‼ _
lb-offset =
  return (const reading 10)
  ⨟ handle perform read ⋆ (return (v Hd))
    `with (λ op → readOffset {Q = ∅ᴴ} {Γ = ∅ᶜ ⟨ ∣ ûₑ ∣̂ᵉ ⟩}
                             {B = Base reading |×| Base reading} op)
    `in (return ⦉ #ᵛ (# 0) , #ᵛ (# 1) ⦊)

ex-lb-offset : Verdict lb-offset
ex-lb-offset = ok (Base reading |×| Base reading) (econst (op-grade read)) refl ≤!

-- `handlers_nested.tpe`, with `write` for both operations: the outer
-- clause runs an inner handler whose clause idles and resumes

nested : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ _
nested = h-in-clause

ex-nested : Verdict nested
ex-nested = ok Unit (econst (op-grade write)) refl ≤!
