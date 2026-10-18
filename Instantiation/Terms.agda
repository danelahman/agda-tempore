------------------------------------------------------------------
-- The instantiation theorem                                    --
--                                                              --
-- An open typing under `Q` is a family of declarative typings, --
-- one per instance satisfying `Q`: for every declarative       --
-- instance `σ` of the type, resource-grade and effect-grade    --
-- variables with `σ ⊨ᴰ Q`, a derivation `Q ∣ Γ ⊢C⦂ C` gives a  --
-- derivation `⟦ Γ ⟧ᶜᵗˣ σ ⊢C⦂ ⟦ C ⟧ᶜ σ` of the same term in the --
-- declarative calculus (`instantiateᶜ`, and `instantiateᵛ` for --
-- values).                                                     --
--                                                              --
-- The typing is built rule by rule, each side condition by the --
-- soundness of entailment and the annotation rules as their    --
-- subjects. A handler clause, typed at a rigid continuation    --
-- grade, is instantiated at every extension `σ ,ᵉᴰ c`, which   --
-- gives the closed clause family.                              --
--                                                              --
-- In the open syntax: for every closed instance `δ` with       --
-- `δ ⊨ Q ∣ []`, the term is typed at                           --
-- `⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⊢C⦂ ⌞ C [ δ ]ᶜ ⌟ᶜ` (`instantiateˢᶜ`,      --
-- `instantiateˢᵛ`), the declarative theorem at `⌞ δ ⌟ˢ`        --
-- through the correspondence of the two kinds of instance.     --
--                                                              --
-- The same term: the closed erasure of the typing is the open  --
-- erasure with its type annotations and box grades forgotten   --
-- (`⌊_⌋ᴿᶜ`, invariant under substitution by `⌊[]⌋ᴿᶜ`).         --
------------------------------------------------------------------

open import Data.Fin using (toℕ)
open import Data.List.Base using ([])
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module Instantiation.Terms (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types     S
open import Syntax.Contexts  S
open import Syntax.Language  S
open import Syntax.Erasure   S hiding (⌊_⌋ᵛ; ⌊_⌋ᶜ; var-pos)
import Syntax.Erasure S as CE

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Language  S
open import TypeInference.Raw.Syntax           S
open import TypeInference.Raw.Subst            S
import TypeInference.Erase S as OE
open import TypeInference.OpenSyntax.Instances S using (_⊨_∣_)

open import Instantiation.Types      S
open import Instantiation.Judgements     S
open import Instantiation.Correspondence S

------------------------------------------------------------------------
-- Raw terms with their annotations and box grades forgotten

mutual

  ⌊_⌋ᴿᵛ : ∀ {Θ n} → RawV Θ n → ErV
  ⌊ var i ⌋ᴿᵛ       = var (toℕ i)
  ⌊ const B c ⌋ᴿᵛ   = const B c
  ⌊ ⋆ ⌋ᴿᵛ           = ⋆
  ⌊ true ⌋ᴿᵛ        = true
  ⌊ false ⌋ᴿᵛ       = false
  ⌊ zero ⌋ᴿᵛ        = zero
  ⌊ succ V ⌋ᴿᵛ      = succ ⌊ V ⌋ᴿᵛ
  ⌊ ⦉ V , W ⦊ ⌋ᴿᵛ    = ⦉ ⌊ V ⌋ᴿᵛ , ⌊ W ⌋ᴿᵛ ⦊
  ⌊ inl V ⌋ᴿᵛ       = inl ⌊ V ⌋ᴿᵛ
  ⌊ inr V ⌋ᴿᵛ       = inr ⌊ V ⌋ᴿᵛ
  ⌊ nil ⌋ᴿᵛ         = nil
  ⌊ cons V W ⌋ᴿᵛ    = cons ⌊ V ⌋ᴿᵛ ⌊ W ⌋ᴿᵛ
  ⌊ lam M ⌋ᴿᵛ       = lam ⌊ M ⌋ᴿᶜ
  ⌊ V ⦂ᵛ A ⌋ᴿᵛ      = ⌊ V ⌋ᴿᵛ

  -- a clause does not depend on the continuation grade, which the raw
  -- term mentions only in annotations

  ⌊_⌋ᴿᶜ : ∀ {Θ n} → RawC Θ n → ErC
  ⌊ return V ⌋ᴿᶜ                = return ⌊ V ⌋ᴿᵛ
  ⌊ M ⨟ N ⌋ᴿᶜ                   = ⌊ M ⌋ᴿᶜ ⨟ ⌊ N ⌋ᴿᶜ
  ⌊ V · W ⌋ᴿᶜ                   = ⌊ V ⌋ᴿᵛ · ⌊ W ⌋ᴿᵛ
  ⌊ match V `in M ⌋ᴿᶜ           = match ⌊ V ⌋ᴿᵛ `in ⌊ M ⌋ᴿᶜ
  ⌊ absurd V ⌋ᴿᶜ                = absurd ⌊ V ⌋ᴿᵛ
  ⌊ if V `then M `else N ⌋ᴿᶜ    = if ⌊ V ⌋ᴿᵛ `then ⌊ M ⌋ᴿᶜ `else ⌊ N ⌋ᴿᶜ
  ⌊ cmp ⋈ V W ⌋ᴿᶜ               = cmp ⋈ ⌊ V ⌋ᴿᵛ ⌊ W ⌋ᴿᵛ
  ⌊ caseℕ V `zero M `succ N ⌋ᴿᶜ = caseℕ ⌊ V ⌋ᴿᵛ `zero ⌊ M ⌋ᴿᶜ `succ ⌊ N ⌋ᴿᶜ
  ⌊ case+ V `inl M `inr N ⌋ᴿᶜ   = case+ ⌊ V ⌋ᴿᵛ `inl ⌊ M ⌋ᴿᶜ `inr ⌊ N ⌋ᴿᶜ
  ⌊ recℕ V M N ⌋ᴿᶜ              = recℕ ⌊ V ⌋ᴿᵛ ⌊ M ⌋ᴿᶜ ⌊ N ⌋ᴿᶜ
  ⌊ caseL V `nil M `cons N ⌋ᴿᶜ  = caseL ⌊ V ⌋ᴿᵛ `nil ⌊ M ⌋ᴿᶜ `cons ⌊ N ⌋ᴿᶜ
  ⌊ recL V M N ⌋ᴿᶜ              = recL ⌊ V ⌋ᴿᵛ ⌊ M ⌋ᴿᶜ ⌊ N ⌋ᴿᶜ
  ⌊ perform op V M ⌋ᴿᶜ          = perform op ⌊ V ⌋ᴿᵛ ⌊ M ⌋ᴿᶜ
  ⌊ delay τ M ⌋ᴿᶜ               = delay τ ⌊ M ⌋ᴿᶜ
  ⌊ handle M `with H `in N ⌋ᴿᶜ  = handle ⌊ M ⌋ᴿᶜ `with (λ op _ → ⌊ H op ⌋ᴿᶜ) `in ⌊ N ⌋ᴿᶜ
  ⌊ unbox i N ⌋ᴿᶜ               = unbox (toℕ i) ⌊ N ⌋ᴿᶜ
  ⌊ box ρ V N ⌋ᴿᶜ               = box ⌊ V ⌋ᴿᵛ ⌊ N ⌋ᴿᶜ
  ⌊ M ⦂ᶜ C ⌋ᴿᶜ                  = ⌊ M ⌋ᴿᶜ

-- Forgetting is invariant under substitution. The handler case compares
-- clause families, functions, and so uses `fun-ext`.

mutual

  ⌊[]⌋ᴿᵛ : ∀ {Θ Θ' n} → (V : RawV Θ n) → (σ : Subst Θ Θ') → ⌊ V [ σ ]ᴿᵛ ⌋ᴿᵛ ≡ ⌊ V ⌋ᴿᵛ
  ⌊[]⌋ᴿᵛ (var i)     σ = refl
  ⌊[]⌋ᴿᵛ (const B c) σ = refl
  ⌊[]⌋ᴿᵛ ⋆           σ = refl
  ⌊[]⌋ᴿᵛ true        σ = refl
  ⌊[]⌋ᴿᵛ false       σ = refl
  ⌊[]⌋ᴿᵛ zero        σ = refl
  ⌊[]⌋ᴿᵛ (succ V)    σ = cong succ (⌊[]⌋ᴿᵛ V σ)
  ⌊[]⌋ᴿᵛ ⦉ V , W ⦊    σ = cong₂ ⦉_,_⦊ (⌊[]⌋ᴿᵛ V σ) (⌊[]⌋ᴿᵛ W σ)
  ⌊[]⌋ᴿᵛ (inl V)     σ = cong inl (⌊[]⌋ᴿᵛ V σ)
  ⌊[]⌋ᴿᵛ (inr V)     σ = cong inr (⌊[]⌋ᴿᵛ V σ)
  ⌊[]⌋ᴿᵛ nil         σ = refl
  ⌊[]⌋ᴿᵛ (cons V W)  σ = cong₂ cons (⌊[]⌋ᴿᵛ V σ) (⌊[]⌋ᴿᵛ W σ)
  ⌊[]⌋ᴿᵛ (lam M)     σ = cong lam (⌊[]⌋ᴿᶜ M σ)
  ⌊[]⌋ᴿᵛ (V ⦂ᵛ A)    σ = ⌊[]⌋ᴿᵛ V σ

  ⌊[]⌋ᴿᶜ : ∀ {Θ Θ' n} → (M : RawC Θ n) → (σ : Subst Θ Θ') → ⌊ M [ σ ]ᴿᶜ ⌋ᴿᶜ ≡ ⌊ M ⌋ᴿᶜ
  ⌊[]⌋ᴿᶜ (return V)                σ = cong return (⌊[]⌋ᴿᵛ V σ)
  ⌊[]⌋ᴿᶜ (M ⨟ N)                   σ = cong₂ _⨟_ (⌊[]⌋ᴿᶜ M σ) (⌊[]⌋ᴿᶜ N σ)
  ⌊[]⌋ᴿᶜ (V · W)                   σ = cong₂ _·_ (⌊[]⌋ᴿᵛ V σ) (⌊[]⌋ᴿᵛ W σ)
  ⌊[]⌋ᴿᶜ (match V `in M)           σ = cong₂ match_`in_ (⌊[]⌋ᴿᵛ V σ) (⌊[]⌋ᴿᶜ M σ)
  ⌊[]⌋ᴿᶜ (absurd V)                σ = cong absurd (⌊[]⌋ᴿᵛ V σ)
  ⌊[]⌋ᴿᶜ (if V `then M `else N)    σ =
    cong₃ if_`then_`else_ (⌊[]⌋ᴿᵛ V σ) (⌊[]⌋ᴿᶜ M σ) (⌊[]⌋ᴿᶜ N σ)
  ⌊[]⌋ᴿᶜ (cmp ⋈ V W)               σ = cong₂ (cmp ⋈) (⌊[]⌋ᴿᵛ V σ) (⌊[]⌋ᴿᵛ W σ)
  ⌊[]⌋ᴿᶜ (caseℕ V `zero M `succ N) σ =
    cong₃ caseℕ_`zero_`succ_ (⌊[]⌋ᴿᵛ V σ) (⌊[]⌋ᴿᶜ M σ) (⌊[]⌋ᴿᶜ N σ)
  ⌊[]⌋ᴿᶜ (case+ V `inl M `inr N)   σ =
    cong₃ case+_`inl_`inr_ (⌊[]⌋ᴿᵛ V σ) (⌊[]⌋ᴿᶜ M σ) (⌊[]⌋ᴿᶜ N σ)
  ⌊[]⌋ᴿᶜ (recℕ V M N)              σ = cong₃ recℕ (⌊[]⌋ᴿᵛ V σ) (⌊[]⌋ᴿᶜ M σ) (⌊[]⌋ᴿᶜ N σ)
  ⌊[]⌋ᴿᶜ (caseL V `nil M `cons N)  σ =
    cong₃ caseL_`nil_`cons_ (⌊[]⌋ᴿᵛ V σ) (⌊[]⌋ᴿᶜ M σ) (⌊[]⌋ᴿᶜ N σ)
  ⌊[]⌋ᴿᶜ (recL V M N)              σ = cong₃ recL (⌊[]⌋ᴿᵛ V σ) (⌊[]⌋ᴿᶜ M σ) (⌊[]⌋ᴿᶜ N σ)
  ⌊[]⌋ᴿᶜ (perform op V M)          σ = cong₂ (perform op) (⌊[]⌋ᴿᵛ V σ) (⌊[]⌋ᴿᶜ M σ)
  ⌊[]⌋ᴿᶜ (delay τ M)               σ = cong (delay τ) (⌊[]⌋ᴿᶜ M σ)
  ⌊[]⌋ᴿᶜ (handle M `with H `in N)  σ =
    cong₃ (λ x y z → handle x `with y `in z)
          (⌊[]⌋ᴿᶜ M σ)
          (fun-ext (λ op → fun-ext (λ _ → ⌊[]⌋ᴿᶜ (H op) (σ ↑ᵉ))))
          (⌊[]⌋ᴿᶜ N σ)
  ⌊[]⌋ᴿᶜ (unbox i N)               σ = cong (unbox (toℕ i)) (⌊[]⌋ᴿᶜ N σ)
  ⌊[]⌋ᴿᶜ (box ρ V N)               σ = cong₂ box (⌊[]⌋ᴿᵛ V σ) (⌊[]⌋ᴿᶜ N σ)
  ⌊[]⌋ᴿᶜ (M ⦂ᶜ C)                  σ = ⌊[]⌋ᴿᶜ M σ

------------------------------------------------------------------------
-- Transport of closed typings, which erasure does not see

castᵛ : ∀ {Γ Γ' A A'} → Γ ≡ Γ' → A ≡ A' → Γ ⊢V⦂ A → Γ' ⊢V⦂ A'
castᵛ refl refl V = V

castᶜ : ∀ {Γ Γ' C C'} → Γ ≡ Γ' → C ≡ C' → Γ ⊢C⦂ C → Γ' ⊢C⦂ C'
castᶜ refl refl M = M

castᵛ-⌊⌋ : ∀ {Γ Γ' A A'} → (p : Γ ≡ Γ') → (q : A ≡ A') → (V : Γ ⊢V⦂ A)
         → CE.⌊ castᵛ p q V ⌋ᵛ ≡ CE.⌊ V ⌋ᵛ
castᵛ-⌊⌋ refl refl V = refl

castᶜ-⌊⌋ : ∀ {Γ Γ' C C'} → (p : Γ ≡ Γ') → (q : C ≡ C') → (M : Γ ⊢C⦂ C)
         → CE.⌊ castᶜ p q M ⌋ᶜ ≡ CE.⌊ M ⌋ᶜ
castᶜ-⌊⌋ refl refl M = refl

------------------------------------------------------------------------
-- The contexts and types of `perform` and of a handler clause

module _ {Θ : Scope} {n : ℕ} (Γ : OCtx Θ n) (σ : DInst Θ) (op : Op) where

  perform-ctx : ⟦ Γ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ ⟧ᶜᵗˣ σ
                ≡ ⟦ Γ ⟧ᶜᵗˣ σ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
  perform-ctx = cong (⟦ Γ ⟧ᶜᵗˣ σ ⟨ mapᵉ (op-grade op) ⟩ ∷_) (⟦⌜ arity op ⌝ᵍ⟧ σ)

  module _ (B : OVType Θ) (c : E) where

    clause-ctx : ⟦ wkᵉ-ctx Γ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                     ∷ [ rconst (mapᵉ (op-grade op)) ]
                         (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ})) ⟧ᶜᵗˣ (σ ,ᵉᴰ c)
                 ≡ ⟦ Γ ⟧ᶜᵗˣ σ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ ⟦ B ⟧ᵛ σ ‼ c)
    clause-ctx =
      cong₃ (λ G P K → G ⟨ ⊤ᵣ ⟩ ∷ P ∷ [ mapᵉ (op-grade op) ] K)
            (⟦wkᵉ⟧ᶜᵗˣ σ c Γ)
            (⟦⌜ param op ⌝ᵍ⟧ (σ ,ᵉᴰ c))
            (cong₂ (λ X Y → X ⇒ Y ‼ c) (⟦⌜ arity op ⌝ᵍ⟧ (σ ,ᵉᴰ c)) (⟦wkᵉ⟧ᵛ σ c B))

    clause-ty : ⟦ wkᵉ-v B ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ})) ⟧ᶜ (σ ,ᵉᴰ c)
                ≡ ⟦ B ⟧ᵛ σ ‼ (op-grade op ·ₑ c)
    clause-ty = cong (_‼ (op-grade op ·ₑ c)) (⟦wkᵉ⟧ᵛ σ c B)

------------------------------------------------------------------------
-- The typing at an instance

-- the var-rule disjunction as the closed rule's side condition

varOK : ∀ {A : VType} {ρ : R} → Eternal A ⊎ (ρ ≾ᵣ uᵣ) → ¬ Eternal A → ρ ≾ᵣ uᵣ
varOK (inj₁ et) ¬et = ⊥-elim (¬et et)
varOK (inj₂ le) ¬et = le

mutual

  instᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
        → (σ : DInst Θ) → σ ⊨ᴰ Q
        → Q ∣ Γ ⊢V⦂ A
        → ⟦ Γ ⟧ᶜᵗˣ σ ⊢V⦂ ⟦ A ⟧ᵛ σ
  instᵛ σ s (var x ok)   = var (varOK (sound-VarOK s ok)) ⟦ x ⟧ˣ
  instᵛ σ s (const B c)  = const c
  instᵛ σ s ⋆            = ⋆
  instᵛ σ s true         = true
  instᵛ σ s false        = false
  instᵛ σ s zero         = zero
  instᵛ σ s (succ V)     = succ (instᵛ σ s V)
  instᵛ σ s ⦉ V , W ⦊     = ⦉ instᵛ σ s V , instᵛ σ s W ⦊
  instᵛ σ s (inl V)      = inl (instᵛ σ s V)
  instᵛ σ s (inr V)      = inr (instᵛ σ s V)
  instᵛ σ s nil          = nil
  instᵛ σ s (cons V W)   = cons (instᵛ σ s V) (instᵛ σ s W)
  instᵛ σ s (lam M)      = lam (instᶜ σ s M)
  instᵛ σ s (annᵛ A V)   = instᵛ σ s V
  instᵛ σ s (subV V p)   = subV (instᵛ σ s V) (sound-<:ᵛ s p)

  instᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
        → (σ : DInst Θ) → σ ⊨ᴰ Q
        → Q ∣ Γ ⊢C⦂ C
        → ⟦ Γ ⟧ᶜᵗˣ σ ⊢C⦂ ⟦ C ⟧ᶜ σ
  instᶜ σ s (return V)                = return (instᵛ σ s V)
  instᶜ σ s (M ⨟ N)                   = instᶜ σ s M ⨟ instᶜ σ s N
  instᶜ σ s (V · W)                   = instᵛ σ s V · instᵛ σ s W
  instᶜ σ s (match V `in M)           = match instᵛ σ s V `in instᶜ σ s M
  instᶜ σ s (absurd V)                = absurd (instᵛ σ s V)
  instᶜ σ s (if V `then M `else N)    = if instᵛ σ s V `then instᶜ σ s M `else instᶜ σ s N
  instᶜ σ s (cmp ⋈ V W et)            = cmp ⋈ (instᵛ σ s V) (instᵛ σ s W) (sound-⊩ᴱ s et)
  instᶜ σ s (caseℕ V `zero M `succ N) =
    caseℕ instᵛ σ s V `zero instᶜ σ s M `succ instᶜ σ s N
  instᶜ σ s (case+ V `inl M `inr N)   =
    case+ instᵛ σ s V `inl instᶜ σ s M `inr instᶜ σ s N
  instᶜ σ s (caseL V `nil M `cons N)  =
    caseL instᵛ σ s V `nil instᶜ σ s M `cons instᶜ σ s N
  instᶜ σ s (recℕ V M N p)            =
    recℕ (instᵛ σ s V) (instᶜ σ s M) (instᶜ σ s N) (sound-≾ₑ s p)
  instᶜ σ s (recL V M N p)            =
    recL (instᵛ σ s V) (instᶜ σ s M) (instᶜ σ s N) (sound-≾ₑ s p)
  instᶜ {Γ = Γ} σ s (perform op V M)  =
    perform op (castᵛ refl (⟦⌜ param op ⌝ᵍ⟧ σ) (instᵛ σ s V))
               (castᶜ (perform-ctx Γ σ op) refl (instᶜ σ s M))
  instᶜ σ s (delay τ M)               = delay τ (instᶜ σ s M)
  instᶜ {Γ = Γ} σ s (handle_`with_`in {B = B} M H N) =
    handle (instᶜ σ s M)
      `with (λ op c → castᶜ (clause-ctx Γ σ op B c) (clause-ty Γ σ op B c)
                         (instᶜ (σ ,ᵉᴰ c) (⊨ᴰ-,ᵉ c s) (H op)))
      `in (instᶜ σ s N)
  instᶜ σ s (unbox x p q N)           =
    unbox ⟦ x ⟧ˣ (sound-≾ᵣ s p) (sound-<:ᵛ s q) (instᶜ σ s N)
  instᶜ σ s (box ρ V N)               = box (instᵛ σ s V) (instᶜ σ s N)
  instᶜ σ s (annᶜ C M)                = instᶜ σ s M
  instᶜ σ s (subC M p)                = subC (instᶜ σ s M) (sound-<:ᶜ s p)

------------------------------------------------------------------------
-- The typing is of the same term

mutual

  instᵛ-⌊⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
           → (σ : DInst Θ) → (s : σ ⊨ᴰ Q)
           → (V : Q ∣ Γ ⊢V⦂ A)
           → CE.⌊ instᵛ σ s V ⌋ᵛ ≡ ⌊ OE.⌊ V ⌋ᵛ ⌋ᴿᵛ
  instᵛ-⌊⌋ σ s (var x ok)   = cong var (⟦⟧ˣ-pos x)
  instᵛ-⌊⌋ σ s (const B c)  = refl
  instᵛ-⌊⌋ σ s ⋆            = refl
  instᵛ-⌊⌋ σ s true         = refl
  instᵛ-⌊⌋ σ s false        = refl
  instᵛ-⌊⌋ σ s zero         = refl
  instᵛ-⌊⌋ σ s (succ V)     = cong succ (instᵛ-⌊⌋ σ s V)
  instᵛ-⌊⌋ σ s ⦉ V , W ⦊     = cong₂ ⦉_,_⦊ (instᵛ-⌊⌋ σ s V) (instᵛ-⌊⌋ σ s W)
  instᵛ-⌊⌋ σ s (inl V)      = cong inl (instᵛ-⌊⌋ σ s V)
  instᵛ-⌊⌋ σ s (inr V)      = cong inr (instᵛ-⌊⌋ σ s V)
  instᵛ-⌊⌋ σ s nil          = refl
  instᵛ-⌊⌋ σ s (cons V W)   = cong₂ cons (instᵛ-⌊⌋ σ s V) (instᵛ-⌊⌋ σ s W)
  instᵛ-⌊⌋ σ s (lam M)      = cong lam (instᶜ-⌊⌋ σ s M)
  instᵛ-⌊⌋ σ s (annᵛ A V)   = instᵛ-⌊⌋ σ s V
  instᵛ-⌊⌋ σ s (subV V p)   = instᵛ-⌊⌋ σ s V

  -- the handler case compares clause families, functions of the operation
  -- and the continuation grade, and so uses `fun-ext`

  instᶜ-⌊⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
           → (σ : DInst Θ) → (s : σ ⊨ᴰ Q)
           → (M : Q ∣ Γ ⊢C⦂ C)
           → CE.⌊ instᶜ σ s M ⌋ᶜ ≡ ⌊ OE.⌊ M ⌋ᶜ ⌋ᴿᶜ
  instᶜ-⌊⌋ σ s (return V)                = cong return (instᵛ-⌊⌋ σ s V)
  instᶜ-⌊⌋ σ s (M ⨟ N)                   = cong₂ _⨟_ (instᶜ-⌊⌋ σ s M) (instᶜ-⌊⌋ σ s N)
  instᶜ-⌊⌋ σ s (V · W)                   = cong₂ _·_ (instᵛ-⌊⌋ σ s V) (instᵛ-⌊⌋ σ s W)
  instᶜ-⌊⌋ σ s (match V `in M)           =
    cong₂ match_`in_ (instᵛ-⌊⌋ σ s V) (instᶜ-⌊⌋ σ s M)
  instᶜ-⌊⌋ σ s (absurd V)                = cong absurd (instᵛ-⌊⌋ σ s V)
  instᶜ-⌊⌋ σ s (if V `then M `else N)    =
    cong₃ if_`then_`else_ (instᵛ-⌊⌋ σ s V) (instᶜ-⌊⌋ σ s M) (instᶜ-⌊⌋ σ s N)
  instᶜ-⌊⌋ σ s (cmp ⋈ V W et)            =
    cong₂ (cmp ⋈) (instᵛ-⌊⌋ σ s V) (instᵛ-⌊⌋ σ s W)
  instᶜ-⌊⌋ σ s (caseℕ V `zero M `succ N) =
    cong₃ caseℕ_`zero_`succ_ (instᵛ-⌊⌋ σ s V) (instᶜ-⌊⌋ σ s M) (instᶜ-⌊⌋ σ s N)
  instᶜ-⌊⌋ σ s (case+ V `inl M `inr N)   =
    cong₃ case+_`inl_`inr_ (instᵛ-⌊⌋ σ s V) (instᶜ-⌊⌋ σ s M) (instᶜ-⌊⌋ σ s N)
  instᶜ-⌊⌋ σ s (caseL V `nil M `cons N)  =
    cong₃ caseL_`nil_`cons_ (instᵛ-⌊⌋ σ s V) (instᶜ-⌊⌋ σ s M) (instᶜ-⌊⌋ σ s N)
  instᶜ-⌊⌋ σ s (recℕ V M N p)            =
    cong₃ recℕ (instᵛ-⌊⌋ σ s V) (instᶜ-⌊⌋ σ s M) (instᶜ-⌊⌋ σ s N)
  instᶜ-⌊⌋ σ s (recL V M N p)            =
    cong₃ recL (instᵛ-⌊⌋ σ s V) (instᶜ-⌊⌋ σ s M) (instᶜ-⌊⌋ σ s N)
  instᶜ-⌊⌋ {Γ = Γ} σ s (perform op V M)  =
    cong₂ (perform op)
          (trans (castᵛ-⌊⌋ refl (⟦⌜ param op ⌝ᵍ⟧ σ) (instᵛ σ s V)) (instᵛ-⌊⌋ σ s V))
          (trans (castᶜ-⌊⌋ (perform-ctx Γ σ op) refl (instᶜ σ s M)) (instᶜ-⌊⌋ σ s M))
  instᶜ-⌊⌋ σ s (delay τ M)               = cong (delay τ) (instᶜ-⌊⌋ σ s M)
  instᶜ-⌊⌋ {Γ = Γ} σ s (handle_`with_`in {B = B} M H N) =
    cong₃ (λ x y z → handle x `with y `in z)
          (instᶜ-⌊⌋ σ s M)
          (fun-ext λ op → fun-ext λ c →
             trans (castᶜ-⌊⌋ (clause-ctx Γ σ op B c) (clause-ty Γ σ op B c)
                             (instᶜ (σ ,ᵉᴰ c) (⊨ᴰ-,ᵉ c s) (H op)))
                   (instᶜ-⌊⌋ (σ ,ᵉᴰ c) (⊨ᴰ-,ᵉ c s) (H op)))
          (instᶜ-⌊⌋ σ s N)
  instᶜ-⌊⌋ σ s (unbox x p q N)           = cong₂ unbox (⟦⟧ˣ-pos x) (instᶜ-⌊⌋ σ s N)
  instᶜ-⌊⌋ σ s (box ρ V N)               = cong₂ box (instᵛ-⌊⌋ σ s V) (instᶜ-⌊⌋ σ s N)
  instᶜ-⌊⌋ σ s (annᶜ C M)                = instᶜ-⌊⌋ σ s M
  instᶜ-⌊⌋ σ s (subC M p)                = instᶜ-⌊⌋ σ s M

------------------------------------------------------------------------
-- The instantiation theorem: an open typing under `Q` is, at every
-- declarative instance satisfying `Q`, a closed typing of the same term

instantiateᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
             → (σ : DInst Θ) → σ ⊨ᴰ Q
             → (D : Q ∣ Γ ⊢V⦂ A)
             → Σ[ D' ∈ ⟦ Γ ⟧ᶜᵗˣ σ ⊢V⦂ ⟦ A ⟧ᵛ σ ] (CE.⌊ D' ⌋ᵛ ≡ ⌊ OE.⌊ D ⌋ᵛ ⌋ᴿᵛ)
instantiateᵛ σ s D = instᵛ σ s D , instᵛ-⌊⌋ σ s D

instantiateᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
             → (σ : DInst Θ) → σ ⊨ᴰ Q
             → (D : Q ∣ Γ ⊢C⦂ C)
             → Σ[ D' ∈ ⟦ Γ ⟧ᶜᵗˣ σ ⊢C⦂ ⟦ C ⟧ᶜ σ ] (CE.⌊ D' ⌋ᶜ ≡ ⌊ OE.⌊ D ⌋ᶜ ⌋ᴿᶜ)
instantiateᶜ σ s D = instᶜ σ s D , instᶜ-⌊⌋ σ s D

------------------------------------------------------------------------
-- The instantiation theorem in the open syntax: at every closed
-- instance `δ` satisfying `Q`, a closed typing in the translation of
-- the instantiated context and type, through `⌞ δ ⌟ˢ`

instantiateˢᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
              → (δ : Subst Θ ∅ˢ) → δ ⊨ Q ∣ []
              → (D : Q ∣ Γ ⊢V⦂ A)
              → Σ[ D' ∈ ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⊢V⦂ ⌞ A [ δ ]ᵛ ⌟ᵛ ] (CE.⌊ D' ⌋ᵛ ≡ ⌊ OE.⌊ D ⌋ᵛ ⌋ᴿᵛ)
instantiateˢᵛ {Γ = Γ} {A} δ s D with instantiateᵛ ⌞ δ ⌟ˢ (⊨→⊨ᴰ s) D
... | D' , e = castᵛ p q D' , trans (castᵛ-⌊⌋ p q D') e
  where
    p = sym (⌞[]⌟ᶜᵗˣ δ Γ)
    q = sym (⌞[]⌟ᵛ δ A)

instantiateˢᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
              → (δ : Subst Θ ∅ˢ) → δ ⊨ Q ∣ []
              → (D : Q ∣ Γ ⊢C⦂ C)
              → Σ[ D' ∈ ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⊢C⦂ ⌞ C [ δ ]ᶜ ⌟ᶜ ] (CE.⌊ D' ⌋ᶜ ≡ ⌊ OE.⌊ D ⌋ᶜ ⌋ᴿᶜ)
instantiateˢᶜ {Γ = Γ} {C = C} δ s D with instantiateᶜ ⌞ δ ⌟ˢ (⊨→⊨ᴰ s) D
... | D' , e = castᶜ p q D' , trans (castᶜ-⌊⌋ p q D') e
  where
    p = sym (⌞[]⌟ᶜᵗˣ δ Γ)
    q = sym (⌞[]⌟ᶜ δ C)
