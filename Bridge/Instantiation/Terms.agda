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
-- `δ ⊨ Q ∣ []`, the term `M [ δ ]ᴿᶜ` is typed at               --
-- `⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⊢C⦂ ⌞ C [ δ ]ᶜ ⌟ᶜ` (`instantiateˢᶜ`,      --
-- `instantiateˢᵛ`), the declarative theorem at `⌞ δ ⌟ˢ`        --
-- through the correspondence of the two kinds of instance.     --
--                                                              --
-- The same term: the closed erasure of the typing is the open  --
-- erasure at `σ`, its type annotations forgotten and its box   --
-- grades evaluated (`⌊_⌋ᴿᶜ`). A raw term substituted by `δ`    --
-- at `σ` is the term at `δ ⨟ᴰ σ` (`⌊[]⌋ᴿᶜ`).                   --
------------------------------------------------------------------

open import Data.Fin using (toℕ)
open import Data.List.Base using ([])
open import Data.Product using (Σ-syntax; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module Bridge.Instantiation.Terms (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Language.Types                 S
open import ClosedCalculus.Syntax.Contexts S
open import ClosedCalculus.Syntax.Terms    S
open import ClosedCalculus.Syntax.Erasure  S hiding (⌊_⌋ᵛ; ⌊_⌋ᶜ; var-pos)
import ClosedCalculus.Syntax.Erasure S as CE

open import OpenCalculus.Syntax.Grades    S
open import OpenCalculus.Syntax.Types     S
open import OpenCalculus.Syntax.Contexts  S
open import OpenCalculus.Syntax.Subst     S
open import OpenCalculus.Hypotheses       S
open import OpenCalculus.Typing           S
open import OpenCalculus.Syntax.Raw       S
open import OpenCalculus.Syntax.Raw.Subst S
import OpenCalculus.Typing.Erasure S as OE
open import OpenCalculus.Hypotheses.Instances S using (_⊨_∣_)

open import Bridge.Instantiation.Types      S
open import Bridge.Instantiation.Judgements     S
open import Bridge.Instantiation.Correspondence S

------------------------------------------------------------------------
-- Raw terms at a declarative instance: annotations forgotten, box
-- grades evaluated

mutual

  ⌊_⌋ᴿᵛ : ∀ {Θ n} → RawV Θ n → DInst Θ → ErV
  ⌊ var i ⌋ᴿᵛ       σ = var (toℕ i)
  ⌊ const B c ⌋ᴿᵛ   σ = const B c
  ⌊ ⋆ ⌋ᴿᵛ           σ = ⋆
  ⌊ true ⌋ᴿᵛ        σ = true
  ⌊ false ⌋ᴿᵛ       σ = false
  ⌊ zero ⌋ᴿᵛ        σ = zero
  ⌊ succ V ⌋ᴿᵛ      σ = succ (⌊ V ⌋ᴿᵛ σ)
  ⌊ ⦉ V , W ⦊ ⌋ᴿᵛ    σ = ⦉ ⌊ V ⌋ᴿᵛ σ , ⌊ W ⌋ᴿᵛ σ ⦊
  ⌊ inl V ⌋ᴿᵛ       σ = inl (⌊ V ⌋ᴿᵛ σ)
  ⌊ inr V ⌋ᴿᵛ       σ = inr (⌊ V ⌋ᴿᵛ σ)
  ⌊ nil ⌋ᴿᵛ         σ = nil
  ⌊ cons V W ⌋ᴿᵛ    σ = cons (⌊ V ⌋ᴿᵛ σ) (⌊ W ⌋ᴿᵛ σ)
  ⌊ lam M ⌋ᴿᵛ       σ = lam (⌊ M ⌋ᴿᶜ σ)
  ⌊ V ⦂ᵛ A ⌋ᴿᵛ      σ = ⌊ V ⌋ᴿᵛ σ

  -- a clause, over one more effect-grade variable, is taken at each
  -- continuation grade

  ⌊_⌋ᴿᶜ : ∀ {Θ n} → RawC Θ n → DInst Θ → ErC
  ⌊ return V ⌋ᴿᶜ                σ = return (⌊ V ⌋ᴿᵛ σ)
  ⌊ M ⨟ N ⌋ᴿᶜ                   σ = ⌊ M ⌋ᴿᶜ σ ⨟ ⌊ N ⌋ᴿᶜ σ
  ⌊ V · W ⌋ᴿᶜ                   σ = ⌊ V ⌋ᴿᵛ σ · ⌊ W ⌋ᴿᵛ σ
  ⌊ match V `in M ⌋ᴿᶜ           σ = match ⌊ V ⌋ᴿᵛ σ `in ⌊ M ⌋ᴿᶜ σ
  ⌊ absurd V ⌋ᴿᶜ                σ = absurd (⌊ V ⌋ᴿᵛ σ)
  ⌊ if V `then M `else N ⌋ᴿᶜ    σ = if ⌊ V ⌋ᴿᵛ σ `then ⌊ M ⌋ᴿᶜ σ `else ⌊ N ⌋ᴿᶜ σ
  ⌊ cmp ⋈ V W ⌋ᴿᶜ               σ = cmp ⋈ (⌊ V ⌋ᴿᵛ σ) (⌊ W ⌋ᴿᵛ σ)
  ⌊ caseℕ V `zero M `succ N ⌋ᴿᶜ σ = caseℕ ⌊ V ⌋ᴿᵛ σ `zero ⌊ M ⌋ᴿᶜ σ `succ ⌊ N ⌋ᴿᶜ σ
  ⌊ case+ V `inl M `inr N ⌋ᴿᶜ   σ = case+ ⌊ V ⌋ᴿᵛ σ `inl ⌊ M ⌋ᴿᶜ σ `inr ⌊ N ⌋ᴿᶜ σ
  ⌊ recℕ V M N ⌋ᴿᶜ              σ = recℕ (⌊ V ⌋ᴿᵛ σ) (⌊ M ⌋ᴿᶜ σ) (⌊ N ⌋ᴿᶜ σ)
  ⌊ caseL V `nil M `cons N ⌋ᴿᶜ  σ = caseL ⌊ V ⌋ᴿᵛ σ `nil ⌊ M ⌋ᴿᶜ σ `cons ⌊ N ⌋ᴿᶜ σ
  ⌊ recL V M N ⌋ᴿᶜ              σ = recL (⌊ V ⌋ᴿᵛ σ) (⌊ M ⌋ᴿᶜ σ) (⌊ N ⌋ᴿᶜ σ)
  ⌊ perform op V M ⌋ᴿᶜ          σ = perform op (⌊ V ⌋ᴿᵛ σ) (⌊ M ⌋ᴿᶜ σ)
  ⌊ delay τ M ⌋ᴿᶜ               σ = delay τ (⌊ M ⌋ᴿᶜ σ)
  ⌊ handle M `with H `in N ⌋ᴿᶜ  σ =
    handle ⌊ M ⌋ᴿᶜ σ `with (λ op c → ⌊ H op ⌋ᴿᶜ (σ ,ᵉᴰ c)) `in (⌊ N ⌋ᴿᶜ σ)
  ⌊ unbox i N ⌋ᴿᶜ               σ = unbox (toℕ i) (⌊ N ⌋ᴿᶜ σ)
  ⌊ box ρ V N ⌋ᴿᶜ               σ = box (⟦ ρ ⟧ʳ σ) (⌊ V ⌋ᴿᵛ σ) (⌊ N ⌋ᴿᶜ σ)
  ⌊ M ⦂ᶜ C ⌋ᴿᶜ                  σ = ⌊ M ⌋ᴿᶜ σ

-- A closed raw term means its value at the empty instance

⌞_⌟ᴿᵛ : ∀ {n} → RawV ∅ˢ n → ErV
⌞ V ⌟ᴿᵛ = ⌊ V ⌋ᴿᵛ ∅ᴰ

⌞_⌟ᴿᶜ : ∀ {n} → RawC ∅ˢ n → ErC
⌞ M ⌟ᴿᶜ = ⌊ M ⌋ᴿᶜ ∅ᴰ

-- Pointwise equal instances give the same term. The handler case
-- compares clause families, functions, and so uses `fun-ext`.

mutual

  ⌊≗⌋ᴿᵛ : ∀ {Θ n} {σ σ' : DInst Θ} → σ ≗ᴰ σ' → (V : RawV Θ n) → ⌊ V ⌋ᴿᵛ σ ≡ ⌊ V ⌋ᴿᵛ σ'
  ⌊≗⌋ᴿᵛ p (var i)     = refl
  ⌊≗⌋ᴿᵛ p (const B c) = refl
  ⌊≗⌋ᴿᵛ p ⋆           = refl
  ⌊≗⌋ᴿᵛ p true        = refl
  ⌊≗⌋ᴿᵛ p false       = refl
  ⌊≗⌋ᴿᵛ p zero        = refl
  ⌊≗⌋ᴿᵛ p (succ V)    = cong succ (⌊≗⌋ᴿᵛ p V)
  ⌊≗⌋ᴿᵛ p ⦉ V , W ⦊    = cong₂ ⦉_,_⦊ (⌊≗⌋ᴿᵛ p V) (⌊≗⌋ᴿᵛ p W)
  ⌊≗⌋ᴿᵛ p (inl V)     = cong inl (⌊≗⌋ᴿᵛ p V)
  ⌊≗⌋ᴿᵛ p (inr V)     = cong inr (⌊≗⌋ᴿᵛ p V)
  ⌊≗⌋ᴿᵛ p nil         = refl
  ⌊≗⌋ᴿᵛ p (cons V W)  = cong₂ cons (⌊≗⌋ᴿᵛ p V) (⌊≗⌋ᴿᵛ p W)
  ⌊≗⌋ᴿᵛ p (lam M)     = cong lam (⌊≗⌋ᴿᶜ p M)
  ⌊≗⌋ᴿᵛ p (V ⦂ᵛ A)    = ⌊≗⌋ᴿᵛ p V

  ⌊≗⌋ᴿᶜ : ∀ {Θ n} {σ σ' : DInst Θ} → σ ≗ᴰ σ' → (M : RawC Θ n) → ⌊ M ⌋ᴿᶜ σ ≡ ⌊ M ⌋ᴿᶜ σ'
  ⌊≗⌋ᴿᶜ p (return V)                = cong return (⌊≗⌋ᴿᵛ p V)
  ⌊≗⌋ᴿᶜ p (M ⨟ N)                   = cong₂ _⨟_ (⌊≗⌋ᴿᶜ p M) (⌊≗⌋ᴿᶜ p N)
  ⌊≗⌋ᴿᶜ p (V · W)                   = cong₂ _·_ (⌊≗⌋ᴿᵛ p V) (⌊≗⌋ᴿᵛ p W)
  ⌊≗⌋ᴿᶜ p (match V `in M)           = cong₂ match_`in_ (⌊≗⌋ᴿᵛ p V) (⌊≗⌋ᴿᶜ p M)
  ⌊≗⌋ᴿᶜ p (absurd V)                = cong absurd (⌊≗⌋ᴿᵛ p V)
  ⌊≗⌋ᴿᶜ p (if V `then M `else N)    =
    cong₃ if_`then_`else_ (⌊≗⌋ᴿᵛ p V) (⌊≗⌋ᴿᶜ p M) (⌊≗⌋ᴿᶜ p N)
  ⌊≗⌋ᴿᶜ p (cmp ⋈ V W)               = cong₂ (cmp ⋈) (⌊≗⌋ᴿᵛ p V) (⌊≗⌋ᴿᵛ p W)
  ⌊≗⌋ᴿᶜ p (caseℕ V `zero M `succ N) =
    cong₃ caseℕ_`zero_`succ_ (⌊≗⌋ᴿᵛ p V) (⌊≗⌋ᴿᶜ p M) (⌊≗⌋ᴿᶜ p N)
  ⌊≗⌋ᴿᶜ p (case+ V `inl M `inr N)   =
    cong₃ case+_`inl_`inr_ (⌊≗⌋ᴿᵛ p V) (⌊≗⌋ᴿᶜ p M) (⌊≗⌋ᴿᶜ p N)
  ⌊≗⌋ᴿᶜ p (recℕ V M N)              = cong₃ recℕ (⌊≗⌋ᴿᵛ p V) (⌊≗⌋ᴿᶜ p M) (⌊≗⌋ᴿᶜ p N)
  ⌊≗⌋ᴿᶜ p (caseL V `nil M `cons N)  =
    cong₃ caseL_`nil_`cons_ (⌊≗⌋ᴿᵛ p V) (⌊≗⌋ᴿᶜ p M) (⌊≗⌋ᴿᶜ p N)
  ⌊≗⌋ᴿᶜ p (recL V M N)              = cong₃ recL (⌊≗⌋ᴿᵛ p V) (⌊≗⌋ᴿᶜ p M) (⌊≗⌋ᴿᶜ p N)
  ⌊≗⌋ᴿᶜ p (perform op V M)          = cong₂ (perform op) (⌊≗⌋ᴿᵛ p V) (⌊≗⌋ᴿᶜ p M)
  ⌊≗⌋ᴿᶜ p (delay τ M)               = cong (delay τ) (⌊≗⌋ᴿᶜ p M)
  ⌊≗⌋ᴿᶜ p (handle M `with H `in N)  =
    cong₃ (λ x y z → handle x `with y `in z)
          (⌊≗⌋ᴿᶜ p M)
          (fun-ext (λ op → fun-ext (λ c → ⌊≗⌋ᴿᶜ (≗ᴰ-,ᵉ p c) (H op))))
          (⌊≗⌋ᴿᶜ p N)
  ⌊≗⌋ᴿᶜ p (unbox i N)               = cong (unbox (toℕ i)) (⌊≗⌋ᴿᶜ p N)
  ⌊≗⌋ᴿᶜ p (box ρ V N)               = cong₃ box (⟦≗⟧ʳ p ρ) (⌊≗⌋ᴿᵛ p V) (⌊≗⌋ᴿᶜ p N)
  ⌊≗⌋ᴿᶜ p (M ⦂ᶜ C)                  = ⌊≗⌋ᴿᶜ p M

-- Substitution: the term `X [ δ ]` at `σ` is `X` at the composite
-- `δ ⨟ᴰ σ`

mutual

  ⌊[]⌋ᴿᵛ : ∀ {Θ Θ' n} → (V : RawV Θ n) → (δ : Subst Θ Θ') → (σ : DInst Θ')
         → ⌊ V [ δ ]ᴿᵛ ⌋ᴿᵛ σ ≡ ⌊ V ⌋ᴿᵛ (δ ⨟ᴰ σ)
  ⌊[]⌋ᴿᵛ (var i)     δ σ = refl
  ⌊[]⌋ᴿᵛ (const B c) δ σ = refl
  ⌊[]⌋ᴿᵛ ⋆           δ σ = refl
  ⌊[]⌋ᴿᵛ true        δ σ = refl
  ⌊[]⌋ᴿᵛ false       δ σ = refl
  ⌊[]⌋ᴿᵛ zero        δ σ = refl
  ⌊[]⌋ᴿᵛ (succ V)    δ σ = cong succ (⌊[]⌋ᴿᵛ V δ σ)
  ⌊[]⌋ᴿᵛ ⦉ V , W ⦊    δ σ = cong₂ ⦉_,_⦊ (⌊[]⌋ᴿᵛ V δ σ) (⌊[]⌋ᴿᵛ W δ σ)
  ⌊[]⌋ᴿᵛ (inl V)     δ σ = cong inl (⌊[]⌋ᴿᵛ V δ σ)
  ⌊[]⌋ᴿᵛ (inr V)     δ σ = cong inr (⌊[]⌋ᴿᵛ V δ σ)
  ⌊[]⌋ᴿᵛ nil         δ σ = refl
  ⌊[]⌋ᴿᵛ (cons V W)  δ σ = cong₂ cons (⌊[]⌋ᴿᵛ V δ σ) (⌊[]⌋ᴿᵛ W δ σ)
  ⌊[]⌋ᴿᵛ (lam M)     δ σ = cong lam (⌊[]⌋ᴿᶜ M δ σ)
  ⌊[]⌋ᴿᵛ (V ⦂ᵛ A)    δ σ = ⌊[]⌋ᴿᵛ V δ σ

  ⌊[]⌋ᴿᶜ : ∀ {Θ Θ' n} → (M : RawC Θ n) → (δ : Subst Θ Θ') → (σ : DInst Θ')
         → ⌊ M [ δ ]ᴿᶜ ⌋ᴿᶜ σ ≡ ⌊ M ⌋ᴿᶜ (δ ⨟ᴰ σ)
  ⌊[]⌋ᴿᶜ (return V)                δ σ = cong return (⌊[]⌋ᴿᵛ V δ σ)
  ⌊[]⌋ᴿᶜ (M ⨟ N)                   δ σ = cong₂ _⨟_ (⌊[]⌋ᴿᶜ M δ σ) (⌊[]⌋ᴿᶜ N δ σ)
  ⌊[]⌋ᴿᶜ (V · W)                   δ σ = cong₂ _·_ (⌊[]⌋ᴿᵛ V δ σ) (⌊[]⌋ᴿᵛ W δ σ)
  ⌊[]⌋ᴿᶜ (match V `in M)           δ σ = cong₂ match_`in_ (⌊[]⌋ᴿᵛ V δ σ) (⌊[]⌋ᴿᶜ M δ σ)
  ⌊[]⌋ᴿᶜ (absurd V)                δ σ = cong absurd (⌊[]⌋ᴿᵛ V δ σ)
  ⌊[]⌋ᴿᶜ (if V `then M `else N)    δ σ =
    cong₃ if_`then_`else_ (⌊[]⌋ᴿᵛ V δ σ) (⌊[]⌋ᴿᶜ M δ σ) (⌊[]⌋ᴿᶜ N δ σ)
  ⌊[]⌋ᴿᶜ (cmp ⋈ V W)               δ σ = cong₂ (cmp ⋈) (⌊[]⌋ᴿᵛ V δ σ) (⌊[]⌋ᴿᵛ W δ σ)
  ⌊[]⌋ᴿᶜ (caseℕ V `zero M `succ N) δ σ =
    cong₃ caseℕ_`zero_`succ_ (⌊[]⌋ᴿᵛ V δ σ) (⌊[]⌋ᴿᶜ M δ σ) (⌊[]⌋ᴿᶜ N δ σ)
  ⌊[]⌋ᴿᶜ (case+ V `inl M `inr N)   δ σ =
    cong₃ case+_`inl_`inr_ (⌊[]⌋ᴿᵛ V δ σ) (⌊[]⌋ᴿᶜ M δ σ) (⌊[]⌋ᴿᶜ N δ σ)
  ⌊[]⌋ᴿᶜ (recℕ V M N)              δ σ =
    cong₃ recℕ (⌊[]⌋ᴿᵛ V δ σ) (⌊[]⌋ᴿᶜ M δ σ) (⌊[]⌋ᴿᶜ N δ σ)
  ⌊[]⌋ᴿᶜ (caseL V `nil M `cons N)  δ σ =
    cong₃ caseL_`nil_`cons_ (⌊[]⌋ᴿᵛ V δ σ) (⌊[]⌋ᴿᶜ M δ σ) (⌊[]⌋ᴿᶜ N δ σ)
  ⌊[]⌋ᴿᶜ (recL V M N)              δ σ =
    cong₃ recL (⌊[]⌋ᴿᵛ V δ σ) (⌊[]⌋ᴿᶜ M δ σ) (⌊[]⌋ᴿᶜ N δ σ)
  ⌊[]⌋ᴿᶜ (perform op V M)          δ σ = cong₂ (perform op) (⌊[]⌋ᴿᵛ V δ σ) (⌊[]⌋ᴿᶜ M δ σ)
  ⌊[]⌋ᴿᶜ (delay τ M)               δ σ = cong (delay τ) (⌊[]⌋ᴿᶜ M δ σ)
  ⌊[]⌋ᴿᶜ (handle M `with H `in N)  δ σ =
    cong₃ (λ x y z → handle x `with y `in z)
          (⌊[]⌋ᴿᶜ M δ σ)
          (fun-ext (λ op → fun-ext (λ c →
             trans (⌊[]⌋ᴿᶜ (H op) (δ ↑ᵉ) (σ ,ᵉᴰ c)) (⌊≗⌋ᴿᶜ (↑ᵉ-⨟ᴰ δ σ c) (H op)))))
          (⌊[]⌋ᴿᶜ N δ σ)
  ⌊[]⌋ᴿᶜ (unbox i N)               δ σ = cong (unbox (toℕ i)) (⌊[]⌋ᴿᶜ N δ σ)
  ⌊[]⌋ᴿᶜ (box ρ V N)               δ σ =
    cong₃ box (⟦[]⟧ʳ δ σ ρ) (⌊[]⌋ᴿᵛ V δ σ) (⌊[]⌋ᴿᶜ N δ σ)
  ⌊[]⌋ᴿᶜ (M ⦂ᶜ C)                  δ σ = ⌊[]⌋ᴿᶜ M δ σ

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
  instᶜ σ s (box ρ V N)               = box (⟦ ρ ⟧ʳ σ) (instᵛ σ s V) (instᶜ σ s N)
  instᶜ σ s (annᶜ C M)                = instᶜ σ s M
  instᶜ σ s (subC M p)                = subC (instᶜ σ s M) (sound-<:ᶜ s p)

------------------------------------------------------------------------
-- The typing is of the same term

mutual

  instᵛ-⌊⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
           → (σ : DInst Θ) → (s : σ ⊨ᴰ Q)
           → (V : Q ∣ Γ ⊢V⦂ A)
           → CE.⌊ instᵛ σ s V ⌋ᵛ ≡ ⌊ OE.⌊ V ⌋ᵛ ⌋ᴿᵛ σ
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
           → CE.⌊ instᶜ σ s M ⌋ᶜ ≡ ⌊ OE.⌊ M ⌋ᶜ ⌋ᴿᶜ σ
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
  instᶜ-⌊⌋ σ s (box ρ V N)               =
    cong₂ (box (⟦ ρ ⟧ʳ σ)) (instᵛ-⌊⌋ σ s V) (instᶜ-⌊⌋ σ s N)
  instᶜ-⌊⌋ σ s (annᶜ C M)                = instᶜ-⌊⌋ σ s M
  instᶜ-⌊⌋ σ s (subC M p)                = instᶜ-⌊⌋ σ s M

------------------------------------------------------------------------
-- The instantiation theorem: an open typing under `Q` is, at every
-- declarative instance satisfying `Q`, a closed typing of the same term

instantiateᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
             → (σ : DInst Θ) → σ ⊨ᴰ Q
             → (D : Q ∣ Γ ⊢V⦂ A)
             → Σ[ D' ∈ ⟦ Γ ⟧ᶜᵗˣ σ ⊢V⦂ ⟦ A ⟧ᵛ σ ] (CE.⌊ D' ⌋ᵛ ≡ ⌊ OE.⌊ D ⌋ᵛ ⌋ᴿᵛ σ)
instantiateᵛ σ s D = instᵛ σ s D , instᵛ-⌊⌋ σ s D

instantiateᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
             → (σ : DInst Θ) → σ ⊨ᴰ Q
             → (D : Q ∣ Γ ⊢C⦂ C)
             → Σ[ D' ∈ ⟦ Γ ⟧ᶜᵗˣ σ ⊢C⦂ ⟦ C ⟧ᶜ σ ] (CE.⌊ D' ⌋ᶜ ≡ ⌊ OE.⌊ D ⌋ᶜ ⌋ᴿᶜ σ)
instantiateᶜ σ s D = instᶜ σ s D , instᶜ-⌊⌋ σ s D

------------------------------------------------------------------------
-- The instantiation theorem in the open syntax: at every closed
-- instance `δ` satisfying `Q`, a closed typing in the translation of
-- the instantiated context and type, through `⌞ δ ⌟ˢ`

instantiateˢᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
              → (δ : Subst Θ ∅ˢ) → δ ⊨ Q ∣ []
              → (D : Q ∣ Γ ⊢V⦂ A)
              → Σ[ D' ∈ ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⊢V⦂ ⌞ A [ δ ]ᵛ ⌟ᵛ ]
                  (CE.⌊ D' ⌋ᵛ ≡ ⌞ OE.⌊ D ⌋ᵛ [ δ ]ᴿᵛ ⌟ᴿᵛ)
instantiateˢᵛ {Γ = Γ} {A} δ s D with instantiateᵛ ⌞ δ ⌟ˢ (⊨→⊨ᴰ s) D
... | D' , e = castᵛ p q D' , trans (castᵛ-⌊⌋ p q D') (trans e (sym (⌊[]⌋ᴿᵛ OE.⌊ D ⌋ᵛ δ ∅ᴰ)))
  where
    p = sym (⌞[]⌟ᶜᵗˣ δ Γ)
    q = sym (⌞[]⌟ᵛ δ A)

instantiateˢᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
              → (δ : Subst Θ ∅ˢ) → δ ⊨ Q ∣ []
              → (D : Q ∣ Γ ⊢C⦂ C)
              → Σ[ D' ∈ ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⊢C⦂ ⌞ C [ δ ]ᶜ ⌟ᶜ ]
                  (CE.⌊ D' ⌋ᶜ ≡ ⌞ OE.⌊ D ⌋ᶜ [ δ ]ᴿᶜ ⌟ᴿᶜ)
instantiateˢᶜ {Γ = Γ} {C = C} δ s D with instantiateᶜ ⌞ δ ⌟ˢ (⊨→⊨ᴰ s) D
... | D' , e = castᶜ p q D' , trans (castᶜ-⌊⌋ p q D') (trans e (sym (⌊[]⌋ᴿᶜ OE.⌊ D ⌋ᶜ δ ∅ᴰ)))
  where
    p = sym (⌞[]⌟ᶜᵗˣ δ Γ)
    q = sym (⌞[]⌟ᶜ δ C)
