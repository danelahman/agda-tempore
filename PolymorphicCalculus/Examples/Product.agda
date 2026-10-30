-------------------------------------------------------------------
-- Inference at a grade of two components                        --
--                                                               --
-- Programs for a grade pairing time with a security level: a    --
-- box is an embargoed report, claimable once enough time has    --
-- passed and only while nothing above its level has been        --
-- touched since it was boxed. None has an annotation.           --
--                                                               --
-- The durations are stepped, `⌜ n ⌝` the duration of `n` ticks. --
-- `embargoed c d` claims a report boxed at `c` after `d` ticks, --
-- `transmitted c op d` after `op` and `d` ticks; `joined-claim` --
-- claims a box handed in after a branch performing one of two   --
-- operations, so its grade is inferred as a join; `publish`     --
-- claims one after calling a function argument and an           --
-- operation, so its scheme's grades mix a variable and a        --
-- constant; `twice op` uses a reading after `op` has run.       --
--                                                               --
-- Every program is written over an arbitrary language; which    --
-- ones are typable, and at which grades, is read off at the     --
-- instance under `Product/`, where the verdicts and schemes are --
-- checked by `refl`.                                            --
-------------------------------------------------------------------

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ)

open import Relation.Nullary.Decidable using (True; toWitness)

open import Grades.Durations using (Stepped)
open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Examples.Product (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S)
  (st : Stepped (GradeSystem.Dur (LanguageSpec.Grades S))) where

open LanguageSpec S
open GradeSystemInterface Grades
  using (R; 𝔻; of-durʳ; of-durᵉ; uᵣ; _·ᵣ_; _·ₑ_; _⊔ₑ_; mapᵉ; _≾ᵣ?_)
  renaming (_≾ᵣ_ to _≾ᴳ_)
open Operations Ops using (Op; param; arity; op-grade)

open import PolymorphicCalculus.Syntax.Grades                S
open import PolymorphicCalculus.Syntax.Types                 S
open import PolymorphicCalculus.Syntax.Contexts              S hiding (Scheme) renaming (_∷_ to _▸_)
open import PolymorphicCalculus.Syntax.GradeSubstitution     S using (idˢ)
open import PolymorphicCalculus.Hypotheses                   S
open import PolymorphicCalculus.Hypotheses.Instances         S using (Satisfiable-∅)
open import PolymorphicCalculus.Typing                       S
open import PolymorphicCalculus.Syntax.Raw                   S
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S using (_[_]ᴿᶜ)
open import PolymorphicCalculus.Typing.Erasure               S using (⌊_⌋ᶜ)
open import PolymorphicCalculus.Inference.Principality       S

open import PolymorphicCalculus.Inference.SolverImpl S hints opEnum using (infer) public
open import PolymorphicCalculus.Examples.Scheme S public
open import PolymorphicCalculus.Examples.Variables

------------------------------------------------------------------
-- The duration of `n` ticks, and its grades

⌜_⌝ : ℕ → 𝔻
⌜ n ⌝ = Stepped.fromℕ st n

⌜_⌝ʳ : ∀ {Θ} → ℕ → RExp Θ
⌜ n ⌝ʳ = rconst (of-durʳ ⌜ n ⌝)

⌜_⌝ᵉ : ∀ {Θ} → ℕ → EExp Θ
⌜ n ⌝ᵉ = econst (of-durᵉ ⌜ n ⌝)

------------------------------------------------------------------
-- A closed derivation in the empty context is a typing

closed : {M : RawC ∅ˢ 0} {C : OCType ∅ˢ} → (D : ∅ᴴ ∣ [] ⊢C⦂ C)
       → ⌊ D ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ → Typable [] M
closed {C = C} D e = typable ∅ˢ idˢ ∅ᴴ C D e Satisfiable-∅

private

  -- A variable no time has passed over

  ok₀ : ∀ {Θ} {Q : Hyps Θ} {A : OVType Θ} → VarOK Q A ûᵣ
  ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

  -- A claim, or a use, after one closed grade below the bound

  after : ∀ {Θ} {Q : Hyps Θ} {c c' : R} → c ≾ᴳ c' → Q ⊩ ûᵣ ·̂ᵣ rconst c ≾̂ᵣ rconst c'
  after p = transᵣ (eqᵣ ≡̂ᵣ-identityˡ) (atomᵣ p)

  -- ... and after two

  after₂ : ∀ {Θ} {Q : Hyps Θ} {c c' c'' : R} → c ·ᵣ c' ≾ᴳ c''
         → Q ⊩ (ûᵣ ·̂ᵣ rconst c) ·̂ᵣ rconst c' ≾̂ᵣ rconst c''
  after₂ p = transᵣ (eqᵣ (≡̂ᵣ-cong ≡̂ᵣ-identityˡ ≡̂ᵣ-refl)) (transᵣ (eqᵣ ≡̂ᵣ-const-·) (atomᵣ p))

------------------------------------------------------------------
-- 1. Claiming an embargoed report
--
--   embargoed c d = box[c] () as x in delay d; unbox x as y in y
--
-- The premise is `⌜ d ⌝ʳ ≾ c`: only time has passed, and a tick
-- touches nothing, so what is weighed is the time.

embargoed : RExp ∅ˢ → ℕ → RawC ∅ˢ 0
embargoed c d = box c ⋆ (delay ⌜ d ⌝ (unbox (var fzero) (return v₀)))

embargoed-D : ∀ c d → of-durʳ ⌜ d ⌝ ≾ᴳ c → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Unit ‼ (⌜ d ⌝ᵉ ·̂ₑ ûₑ)
embargoed-D c d p =
  box (rconst c) ⋆ (delay ⌜ d ⌝ (unbox (res-var {z = Tl-⟨⟩ Hd}) (after p) (return (var Hd ok₀))))

embargoed-typable : ∀ c d → True (of-durʳ ⌜ d ⌝ ≾ᵣ? c) → Typable [] (embargoed (rconst c) d)
embargoed-typable c d p = closed (embargoed-D c d (toWitness p)) refl

expected-embargoed : ℕ → Scheme
expected-embargoed d = ∀[ 0 , 0 , 0 ] ⊤ ⟹ Unit ‼ ⌜ d ⌝ᵉ

------------------------------------------------------------------
-- 2. Claiming it after an operation
--
--   transmitted c op d p = box[c] () as x in op p; delay d; unbox x as y in y
--
-- The premise is `op-grade op · ⌜ d ⌝ʳ ≾ c`, both components at
-- once: the operation's time and the ticks against the embargo, the
-- level the operation touches against the report's.

transmitted : RExp ∅ˢ → Op → ℕ → RawC ∅ˢ 0
transmitted c op d =
  return (lam (box c ⋆ (perform op v₁ (delay ⌜ d ⌝ (unbox (var (fsuc fzero)) (return v₀))))))

transmitted-D : ∀ c op d → mapᵉ (op-grade op) ·ᵣ of-durʳ ⌜ d ⌝ ≾ᴳ c
              → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂
                  (⌜ param op ⌝ᵍ ⇒ Unit ‼ (econst (op-grade op) ·̂ₑ (⌜ d ⌝ᵉ ·̂ₑ ûₑ))) ‼ ûₑ
transmitted-D c op d p =
  return (lam (box (rconst c) ⋆
    (perform op (var (Tl-∷ Hd) ok₀)
      (delay ⌜ d ⌝ (unbox (res-var {z = Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))}) (after₂ p)
                  (return (var Hd ok₀)))))))

transmitted-typable : ∀ c op d → True ((mapᵉ (op-grade op) ·ᵣ of-durʳ ⌜ d ⌝) ≾ᵣ? c)
                    → Typable [] (transmitted (rconst c) op d)
transmitted-typable c op d p = closed (transmitted-D c op d (toWitness p)) refl

expected-transmitted : Op → ℕ → Scheme
expected-transmitted op d =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹
    (⌜ param op ⌝ᵍ ⇒ Unit ‼ econst (op-grade op ·ₑ of-durᵉ ⌜ d ⌝)) ‼ ûₑ

------------------------------------------------------------------
-- 3. A branch joining levels
--
--   joined-claim op₀ op₁ op₂ b c =
--     let r = op₀ () in (if c then op₁ r else op₂ r); unbox b as y in y
--
-- The claim waits for `op₀` and then for either branch, so the
-- least box grade is `op₀ · (op₁ ⊔ op₂)`, and so is the effect: the
-- join keeps the shorter time and the higher level.

joined-claim : Op → Op → Op → RawC ∅ˢ 0
joined-claim op₀ op₁ op₂ =
  return (lam (return (lam
    (perform op₀ ⋆
      ((if v₁ `then perform op₁ v₀ (return ⋆) `else perform op₂ v₀ (return ⋆))
       ⨟ unbox (var (fsuc (fsuc (fsuc fzero)))) (return v₀))))))

expected-joined-claim : Op → Op → Op → Scheme
expected-joined-claim op₀ op₁ op₂ =
  ∀[ 1 , 0 , 0 ] ⊤ ⟹
    ([ rconst (mapᵉ g) ] α₀ ⇒ (Bool ⇒ α₀ ‼ econst g) ‼ ûₑ) ‼ ûₑ
  where
    g = op-grade op₀ ·ₑ (op-grade op₁ ⊔ₑ op-grade op₂)

------------------------------------------------------------------
-- 4. A higher-order function
--
--   publish op f b = let r = f () in op r; unbox b as y in y
--
-- The box is claimed after whatever `f` does and after `op`, so its
-- least grade is `op-grade op · ∣ ε₀ ∣`, `ε₀` being `f`'s effect:
-- the scheme asks for a report that outlasts, in both components,
-- the function it is handed and the operation.

publish : Op → RawC ∅ˢ 0
publish op =
  return (lam (return (lam
    ((v₁ · ⋆) ⨟ perform op v₀ (unbox (var (fsuc (fsuc fzero))) (return v₀))))))

expected-publish : Op → Scheme
expected-publish op =
  ∀[ 1 , 0 , 1 ] ⊤ ⟹
    ((Unit ⇒ ⌜ param op ⌝ᵍ ‼ ε₀)
     ⇒ ([ rconst (mapᵉ (op-grade op)) ·̂ᵣ ∣ ε₀ ∣̂ᵉ ] α₀ ⇒ α₀ ‼ (econst (op-grade op) ·̂ₑ ε₀)) ‼ ûₑ)
    ‼ ûₑ

------------------------------------------------------------------
-- 5. A reading used after an operation
--
--   twice op r = op r; op r
--
-- The second `op r` uses `r` under the lock `⟨ op-grade op ⟩`, and a
-- reading is not eternal, so `var` asks for `op-grade op ≾ uᵣ`.

twice : Op → RawC ∅ˢ 0
twice op = return (lam (perform op v₀ (perform op v₁ (return ⋆))))

twice-D : ∀ op → mapᵉ (op-grade op) ≾ᴳ uᵣ
        → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂
            (⌜ param op ⌝ᵍ ⇒ Unit ‼ (econst (op-grade op) ·̂ₑ (econst (op-grade op) ·̂ₑ ûₑ))) ‼ ûₑ
twice-D op q =
  return (lam (perform op (var Hd ok₀)
    (perform op (var (Tl-∷ (Tl-⟨⟩ Hd)) (≾ᵘ-ok (after q))) (return ⋆))))

twice-typable : ∀ op → True (mapᵉ (op-grade op) ≾ᵣ? uᵣ) → Typable [] (twice op)
twice-typable op q = closed (twice-D op (toWitness q)) refl

expected-twice : Op → Scheme
expected-twice op =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹ (⌜ param op ⌝ᵍ ⇒ Unit ‼ econst (op-grade op ·ₑ op-grade op)) ‼ ûₑ
