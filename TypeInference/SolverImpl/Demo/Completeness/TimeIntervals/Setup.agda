--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows: the setup.               --
--                                                                            --
-- `Generic` at `Worked.Spec`, an answer of each operation, and the clause    --
-- families the entries share.                                                --
--------------------------------------------------------------------------------

open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.Worked.Operations using (read; write; send)
open import Syntax.Grades.Example.Worked.Spec using (spec; reading)

open import TypeInference.Scopes

open import TypeInference.SolverImpl.Demo.TimeIntervals using (ops₃)

import TypeInference.SolverImpl.Demo.Completeness.Generic

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Setup where

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

-- a constant effect of `k` ticks

d : ℕ → ∀ {Θ} → EExp Θ
d k = econst (of-natᵉ k)

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
