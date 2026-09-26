------------------------------------------------------------------
-- Inference at a grade of two components                         --
--                                                                --
-- Programs for a grade pairing time with a security level: a     --
-- box is an embargoed report, claimable once enough time has     --
-- passed and only while nothing above its level has been         --
-- touched since it was boxed. None has an annotation.            --
--                                                                --
-- `embargoed c d` claims a report boxed at `c` after `d` ticks,  --
-- `transmitted c op d` after `op` and `d` ticks; `joined-claim`  --
-- claims a box handed in after a branch performing one of two    --
-- operations, so its grade is inferred as a join; `publish`      --
-- claims one after calling a function argument and an            --
-- operation, so its scheme's grades mix a variable and a         --
-- constant; `twice op` uses a reading after `op` has run.        --
--                                                                --
-- Every program is written over an arbitrary language; which     --
-- ones are typable, and at which grades, is read off at the      --
-- instance under `Product/`, where the verdicts and schemes are  --
-- checked by `refl`.                                             --
------------------------------------------------------------------

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ)

open import Relation.Nullary.Decidable using (True; toWitness)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.Examples.Product (S : LanguageSpec) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades
  using (R; of-natʳ; of-natᵉ; uᵣ; _·ᵣ_; _·ₑ_; _⊔ₑ_; mapᵉ; _≾ᵣ?_)
  renaming (_≾ᵣ_ to _≾ᴳ_)
open Operations Ops using (Op; param; arity; op-grade)

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S renaming (_∷_ to _▸_)
open import TypeInference.OpenSyntax.Subst     S using (idˢ)
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S using (Satisfiable-∅)
open import TypeInference.OpenSyntax.Language  S
open import TypeInference.Raw.Syntax           S
open import TypeInference.Raw.Subst            S using (_[_]ᴿᶜ)
open import TypeInference.Erase                S using (⌊_⌋ᶜ)
open import TypeInference.Principality         S

open import TypeInference.SolverImpl S opEnum using (infer) public
open import TypeInference.Examples.Report S public
open import TypeInference.Examples.Variables

------------------------------------------------------------------
-- Grades of `n` ticks

⌜_⌝ʳ : ∀ {Θ} → ℕ → RExp Θ
⌜ n ⌝ʳ = rconst (of-natʳ n)

⌜_⌝ᵉ : ∀ {Θ} → ℕ → EExp Θ
⌜ n ⌝ᵉ = econst (of-natᵉ n)

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
embargoed c d = box c ⋆ (delay d (unbox fzero (return v₀)))

embargoed-D : ∀ c d → of-natʳ d ≾ᴳ c → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂ Unit ‼ (⌜ d ⌝ᵉ ·̂ₑ ûₑ)
embargoed-D c d p =
  box (rconst c) ⋆ (delay d (unbox (Tl-⟨⟩ Hd) (after p) (<:̂ᵛ-refl _) (return (var Hd ok₀))))

embargoed-typable : ∀ c d → True (of-natʳ d ≾ᵣ? c) → Typable [] (embargoed (rconst c) d)
embargoed-typable c d p = closed (embargoed-D c d (toWitness p)) refl

expected-embargoed : ℕ → Report
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
  return (lam (box c ⋆ (perform op v₁ (delay d (unbox (fsuc fzero) (return v₀))))))

transmitted-D : ∀ c op d → mapᵉ (op-grade op) ·ᵣ of-natʳ d ≾ᴳ c
              → ∅ᴴ {∅ˢ} ∣ [] ⊢C⦂
                  (⌜ param op ⌝ᵍ ⇒ Unit ‼ (econst (op-grade op) ·̂ₑ (⌜ d ⌝ᵉ ·̂ₑ ûₑ))) ‼ ûₑ
transmitted-D c op d p =
  return (lam (box (rconst c) ⋆
    (perform op (var (Tl-∷ Hd) ok₀)
      (delay d (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) (after₂ p) (<:̂ᵛ-refl _)
                  (return (var Hd ok₀)))))))

transmitted-typable : ∀ c op d → True ((mapᵉ (op-grade op) ·ᵣ of-natʳ d) ≾ᵣ? c)
                    → Typable [] (transmitted (rconst c) op d)
transmitted-typable c op d p = closed (transmitted-D c op d (toWitness p)) refl

expected-transmitted : Op → ℕ → Report
expected-transmitted op d =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹
    (⌜ param op ⌝ᵍ ⇒ Unit ‼ econst (op-grade op ·ₑ of-natᵉ d)) ‼ ûₑ

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
       ⨟ unbox (fsuc (fsuc (fsuc fzero))) (return v₀))))))

expected-joined-claim : Op → Op → Op → Report
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
    ((v₁ · ⋆) ⨟ perform op v₀ (unbox (fsuc (fsuc fzero)) (return v₀))))))

expected-publish : Op → Report
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

expected-twice : Op → Report
expected-twice op =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹ (⌜ param op ⌝ᵍ ⇒ Unit ‼ econst (op-grade op ·ₑ op-grade op)) ‼ ûₑ
