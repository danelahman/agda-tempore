------------------------------------------------------------------------
-- Inference at a grade of two components                             --
--                                                                    --
-- A grade pairing time with a lattice: a box is claimable while the  --
-- time passed is within its bound, from below or from above, and     --
-- only while nothing above its level has been touched since it was   --
-- boxed. `⌜ n ⌝` is the duration of `n` ticks.                       --
--                                                                    --
-- The examples, in five numbered groups                              --
--   embargoed c d        a box of grade `c` claimed after `d` ticks; --
--                        a tick touches no level                     --
--   transmitted c op d   the same claim after an operation and `d`   --
--                        ticks, checked in time and in level at once --
--   joined-claim         a claim after one operation and then one    --
--                        of two more, by branch; the box's grade     --
--                        and the effect join the two branches        --
--   publish op           a higher-order function: the box's grade    --
--                        mixes the argument's effect with a constant --
--   twice op             a reading used again after an operation     --
--                                                                    --
-- How to read them                                                   --
--   Each program is written above its definition in ordinary syntax, --
--   with what it needs. The modules under `Product/` run inference   --
--   at time bounded from below and from above, each paired with a    --
--   lattice level, and check each answer with `refl`:                --
--     publish-reported :                                             --
--       schemeOf (infer [] (publish send))                           --
--         ≡ just (expected-publish send)                             --
--   A refused claim comes with the verdict `infer [] p ≡ untypable`  --
--   and the proof `¬ Typable [] p` drawn from it.                    --
------------------------------------------------------------------------

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
  using (R; 𝔻; ιᵣ; ιₑ; 𝟏ᵣ; _·ᵣ_; _·ₑ_; _⊔ₑ_; ∣_∣ᵉ; _≾ᵣ?_)
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
⌜ n ⌝ʳ = rconst (ιᵣ ⌜ n ⌝)

⌜_⌝ᵉ : ∀ {Θ} → ℕ → EExp Θ
⌜ n ⌝ᵉ = econst (ιₑ ⌜ n ⌝)

------------------------------------------------------------------
-- A closed derivation in the empty context is a typing

closed : {M : RawC ∅ˢ 0} {C : OCType ∅ˢ} → (D : ∅ᴴ ∣ [] ⊢ᶜ⦂ C)
       → ⌊ D ⌋ᶜ ≡ M [ idˢ ]ᴿᶜ → Typable [] M
closed {C = C} D e = typable ∅ˢ idˢ ∅ᴴ C D e Satisfiable-∅

private

  -- A variable no time has passed over

  ok₀ : ∀ {Θ} {Q : Hyps Θ} {A : OVType Θ} → Q ⊩ A Et∨≾ᵘ 𝟏̂ᵣ
  ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

  -- A claim, or a use, after one closed grade below the bound

  after : ∀ {Θ} {Q : Hyps Θ} {c c' : R} → c ≾ᴳ c' → Q ⊩ 𝟏̂ᵣ ·̂ᵣ rconst c ≾̂ᵣ rconst c'
  after p = transᵣ (eqᵣ ≡̂ᵣ-identityˡ) (atomᵣ p)

  -- ... and after two

  after₂ : ∀ {Θ} {Q : Hyps Θ} {c c' c'' : R} → c ·ᵣ c' ≾ᴳ c''
         → Q ⊩ (𝟏̂ᵣ ·̂ᵣ rconst c) ·̂ᵣ rconst c' ≾̂ᵣ rconst c''
  after₂ p = transᵣ (eqᵣ (≡̂ᵣ-cong ≡̂ᵣ-identityˡ ≡̂ᵣ-refl)) (transᵣ (eqᵣ ≡̂ᵣ-const-·) (atomᵣ p))

------------------------------------------------------------------
-- 1. Claiming an embargoed report
--
--   embargoed c d = box[c] () as x in delay d; unbox x as y in y
--
-- `⌜ d ⌝ʳ ≾ c`: a tick touches no level.

embargoed : RExp ∅ˢ → ℕ → RawC ∅ˢ 0
embargoed c d = box c ⋆ (delay ⌜ d ⌝ (unbox (var fzero) (return v₀)))

embargoed-D : ∀ c d → ιᵣ ⌜ d ⌝ ≾ᴳ c → ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂ unit ! (⌜ d ⌝ᵉ ·̂ₑ 𝟏̂ₑ)
embargoed-D c d p =
  box (rconst c) ⋆ (delay ⌜ d ⌝ (unbox (res-var (Tl-⟨⟩ Hd)) (after p) (return (var Hd ok₀))))

embargoed-typable : ∀ c d → True (ιᵣ ⌜ d ⌝ ≾ᵣ? c) → Typable [] (embargoed (rconst c) d)
embargoed-typable c d p = closed (embargoed-D c d (toWitness p)) refl

expected-embargoed : ℕ → Scheme
expected-embargoed d = ∀[ 0 , 0 , 0 ] ⊤ ⟹ unit ! ⌜ d ⌝ᵉ

------------------------------------------------------------------
-- 2. Claiming it after an operation
--
--   transmitted c op d p = box[c] () as x in op p; delay d; unbox x as y in y
--
-- `op-grade op · ⌜ d ⌝ʳ ≾ c`, in time and in level at once.

transmitted : RExp ∅ˢ → Op → ℕ → RawC ∅ˢ 0
transmitted c op d =
  return (fun (box c ⋆ (perform op v₁ (delay ⌜ d ⌝ (unbox (var (fsuc fzero)) (return v₀))))))

transmitted-D : ∀ c op d → ∣ op-grade op ∣ᵉ ·ᵣ ιᵣ ⌜ d ⌝ ≾ᴳ c
              → ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂
                  (⌜ param op ⌝ᵍ ⇒ unit ! (econst (op-grade op) ·̂ₑ (⌜ d ⌝ᵉ ·̂ₑ 𝟏̂ₑ))) ! 𝟏̂ₑ
transmitted-D c op d p =
  return (fun (box (rconst c) ⋆
    (perform op (var (Tl-∷ Hd) ok₀)
      (delay ⌜ d ⌝ (unbox (res-var (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) (after₂ p)
                  (return (var Hd ok₀)))))))

transmitted-typable : ∀ c op d → True ((∣ op-grade op ∣ᵉ ·ᵣ ιᵣ ⌜ d ⌝) ≾ᵣ? c)
                    → Typable [] (transmitted (rconst c) op d)
transmitted-typable c op d p = closed (transmitted-D c op d (toWitness p)) refl

expected-transmitted : Op → ℕ → Scheme
expected-transmitted op d =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹
    (⌜ param op ⌝ᵍ ⇒ unit ! econst (op-grade op ·ₑ ιₑ ⌜ d ⌝)) ! 𝟏̂ₑ

------------------------------------------------------------------
-- 3. A branch joining levels
--
--   joined-claim op₀ op₁ op₂ b c =
--     let r = op₀ () in (if c then op₁ r else op₂ r); unbox b as y in y
--
-- The box's grade and the effect are `op₀ · (op₁ ⊔ op₂)`.

joined-claim : Op → Op → Op → RawC ∅ˢ 0
joined-claim op₀ op₁ op₂ =
  return (fun (return (fun
    (perform op₀ ⋆
      ((if v₁ `then perform op₁ v₀ (return ⋆) `else perform op₂ v₀ (return ⋆))
       ⨟ unbox (var (fsuc (fsuc (fsuc fzero)))) (return v₀))))))

expected-joined-claim : Op → Op → Op → Scheme
expected-joined-claim op₀ op₁ op₂ =
  ∀[ 1 , 0 , 0 ] ⊤ ⟹
    ([ rconst ∣ g ∣ᵉ ] α₀ ⇒ (bool ⇒ α₀ ! econst g) ! 𝟏̂ₑ) ! 𝟏̂ₑ
  where
    g = op-grade op₀ ·ₑ (op-grade op₁ ⊔ₑ op-grade op₂)

------------------------------------------------------------------
-- 4. A higher-order function
--
--   publish op f b = let r = f () in op r; unbox b as y in y
--
-- The box's grade is `op-grade op · ∣ ε₀ ∣`, `ε₀` being `f`'s effect:
-- a variable mixed with a constant.

publish : Op → RawC ∅ˢ 0
publish op =
  return (fun (return (fun
    ((v₁ · ⋆) ⨟ perform op v₀ (unbox (var (fsuc (fsuc fzero))) (return v₀))))))

expected-publish : Op → Scheme
expected-publish op =
  ∀[ 1 , 0 , 1 ] ⊤ ⟹
    ((unit ⇒ ⌜ param op ⌝ᵍ ! ε₀)
     ⇒ ([ rconst ∣ op-grade op ∣ᵉ ·̂ᵣ ∣ ε₀ ∣̂ᵉ ] α₀ ⇒ α₀ ! (econst (op-grade op) ·̂ₑ ε₀)) ! 𝟏̂ₑ)
    ! 𝟏̂ₑ

------------------------------------------------------------------
-- 5. A reading used after an operation
--
--   twice op r = op r; op r
--
-- A reading is noneternal: `var` asks `op-grade op ≾ 𝟏ᵣ`.

twice : Op → RawC ∅ˢ 0
twice op = return (fun (perform op v₀ (perform op v₁ (return ⋆))))

twice-D : ∀ op → ∣ op-grade op ∣ᵉ ≾ᴳ 𝟏ᵣ
        → ∅ᴴ {∅ˢ} ∣ [] ⊢ᶜ⦂
            (⌜ param op ⌝ᵍ ⇒ unit ! (econst (op-grade op) ·̂ₑ (econst (op-grade op) ·̂ₑ 𝟏̂ₑ))) ! 𝟏̂ₑ
twice-D op q =
  return (fun (perform op (var Hd ok₀)
    (perform op (var (Tl-∷ (Tl-⟨⟩ Hd)) (≾ᵘ-ok (after q))) (return ⋆))))

twice-typable : ∀ op → True (∣ op-grade op ∣ᵉ ≾ᵣ? 𝟏ᵣ) → Typable [] (twice op)
twice-typable op q = closed (twice-D op (toWitness q)) refl

expected-twice : Op → Scheme
expected-twice op =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹ (⌜ param op ⌝ᵍ ⇒ unit ! econst (op-grade op ·ₑ op-grade op)) ! 𝟏̂ₑ
