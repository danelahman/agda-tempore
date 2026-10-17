------------------------------------------------------------------
-- From open derivations to closed typings                      --
--                                                              --
-- An open derivation `Q ∣ Γ ⊢C⦂ C` at a closed instance `δ`    --
-- satisfying `Q` is a closed typing                            --
-- `⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⊢C⦂ ⌞ C [ δ ]ᶜ ⌟ᶜ` of the same term       --
-- (`bridge`). The translation is rule by rule: each grade      --
-- expression goes to its value at `δ`, each side condition to  --
-- its instance, and the annotation rules to their subjects. A  --
-- handler clause, typed at a rigid continuation grade, is      --
-- translated at each closed grade `c` by instantiating the     --
-- rigid to `econst c`, which gives the closed clause family.   --
--                                                              --
-- The same term: the closed erasure of the translation is the  --
-- open erasure with its type annotations and box grades        --
-- forgotten (`⌊_⌋ᴿᶜ`).                                         --
------------------------------------------------------------------

open import Data.Fin using (toℕ)
open import Data.List.Base using ([])
open import Data.List.Relation.Unary.All using () renaming (_∷_ to _∷ᴬ_)
open import Data.Product using (Σ-syntax; _,_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module Bridge.Terms (S : LanguageSpec) where

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
open import TypeInference.OpenSyntax.Instances S
open import TypeInference.OpenSyntax.Language  S
open import TypeInference.Raw.Syntax           S
open import TypeInference.Raw.Subst            S
import TypeInference.Erase S as OE

open import Bridge.Types      S
open import Bridge.Judgements S

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

module _ {Θ : Scope} {n : ℕ} (Γ : OCtx Θ n) (δ : Subst Θ ∅ˢ) (op : Op) where

  perform-ctx : ⌞ (Γ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ) [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ
                ≡ ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
  perform-ctx = cong (⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⟨ mapᵉ (op-grade op) ⟩ ∷_) (⌞⌜ arity op ⌝ᵍ⌟ δ)

  module _ (B : OVType Θ) (c : E) where

    private
      δ' : Subst (Θ +e) ∅ˢ
      δ' = δ ,ᵉ econst c

    clause-ctx : ⌞ (wkᵉ-ctx Γ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                     ∷ [ rconst (mapᵉ (op-grade op)) ]
                         (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ}))) [ δ' ]ᶜᵗˣ ⌟ᶜᵗˣ
                 ≡ ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ ⌞ B [ δ ]ᵛ ⌟ᵛ ‼ c)
    clause-ctx =
      cong₃ (λ G P K → G ⟨ ⊤ᵣ ⟩ ∷ P ∷ [ mapᵉ (op-grade op) ] K)
            (cong ⌞_⌟ᶜᵗˣ (wk-,ᵉ-ctx δ (econst c) Γ))
            (⌞⌜ param op ⌝ᵍ⌟ δ')
            (cong₂ (λ X Y → X ⇒ Y ‼ c) (⌞⌜ arity op ⌝ᵍ⌟ δ') (cong ⌞_⌟ᵛ (wk-,ᵉ-v δ (econst c) B)))

    clause-ty : ⌞ (wkᵉ-v B ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ}))) [ δ' ]ᶜ ⌟ᶜ
                ≡ ⌞ B [ δ ]ᵛ ⌟ᵛ ‼ (op-grade op ·ₑ c)
    clause-ty = cong (_‼ (op-grade op ·ₑ c)) (cong ⌞_⌟ᵛ (wk-,ᵉ-v δ (econst c) B))

------------------------------------------------------------------------
-- The bridge

mutual

  bridgeᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
          → (δ : Subst Θ ∅ˢ) → ∅ᴴ ⊩ᴴ Q [ δ ]
          → Q ∣ Γ ⊢V⦂ A
          → ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⊢V⦂ ⌞ A [ δ ]ᵛ ⌟ᵛ
  bridgeᵛ δ h (var x ok)   = var (inst-VarOK⌞⌟ h ok) var⌞ x ⌟
  bridgeᵛ δ h (const B c)  = const c
  bridgeᵛ δ h ⋆            = ⋆
  bridgeᵛ δ h true         = true
  bridgeᵛ δ h false        = false
  bridgeᵛ δ h zero         = zero
  bridgeᵛ δ h (succ V)     = succ (bridgeᵛ δ h V)
  bridgeᵛ δ h ⦉ V , W ⦊     = ⦉ bridgeᵛ δ h V , bridgeᵛ δ h W ⦊
  bridgeᵛ δ h (inl V)      = inl (bridgeᵛ δ h V)
  bridgeᵛ δ h (inr V)      = inr (bridgeᵛ δ h V)
  bridgeᵛ δ h nil          = nil
  bridgeᵛ δ h (cons V W)   = cons (bridgeᵛ δ h V) (bridgeᵛ δ h W)
  bridgeᵛ δ h (lam M)      = lam (bridgeᶜ δ h M)
  bridgeᵛ δ h (annᵛ A V)   = bridgeᵛ δ h V
  bridgeᵛ δ h (subV V p)   = subV (bridgeᵛ δ h V) (inst-<:ᵛ h p)

  bridgeᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
          → (δ : Subst Θ ∅ˢ) → ∅ᴴ ⊩ᴴ Q [ δ ]
          → Q ∣ Γ ⊢C⦂ C
          → ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⊢C⦂ ⌞ C [ δ ]ᶜ ⌟ᶜ
  bridgeᶜ δ h (return V)                = return (bridgeᵛ δ h V)
  bridgeᶜ δ h (M ⨟ N)                   = bridgeᶜ δ h M ⨟ bridgeᶜ δ h N
  bridgeᶜ δ h (V · W)                   = bridgeᵛ δ h V · bridgeᵛ δ h W
  bridgeᶜ δ h (match V `in M)           = match bridgeᵛ δ h V `in bridgeᶜ δ h M
  bridgeᶜ δ h (absurd V)                = absurd (bridgeᵛ δ h V)
  bridgeᶜ δ h (if V `then M `else N)    =
    if bridgeᵛ δ h V `then bridgeᶜ δ h M `else bridgeᶜ δ h N
  bridgeᶜ δ h (cmp ⋈ V W et)            = cmp ⋈ (bridgeᵛ δ h V) (bridgeᵛ δ h W) (inst-⊩ᴱ h et)
  bridgeᶜ δ h (caseℕ V `zero M `succ N) =
    caseℕ bridgeᵛ δ h V `zero bridgeᶜ δ h M `succ bridgeᶜ δ h N
  bridgeᶜ δ h (case+ V `inl M `inr N)   =
    case+ bridgeᵛ δ h V `inl bridgeᶜ δ h M `inr bridgeᶜ δ h N
  bridgeᶜ δ h (caseL V `nil M `cons N)  =
    caseL bridgeᵛ δ h V `nil bridgeᶜ δ h M `cons bridgeᶜ δ h N
  bridgeᶜ δ h (recℕ V M N p)            =
    recℕ (bridgeᵛ δ h V) (bridgeᶜ δ h M) (bridgeᶜ δ h N) (inst-≾ₑ h p)
  bridgeᶜ δ h (recL V M N p)            =
    recL (bridgeᵛ δ h V) (bridgeᶜ δ h M) (bridgeᶜ δ h N) (inst-≾ₑ h p)
  bridgeᶜ {Γ = Γ} δ h (perform op V M)  =
    perform op (castᵛ refl (⌞⌜ param op ⌝ᵍ⌟ δ) (bridgeᵛ δ h V))
               (castᶜ (perform-ctx Γ δ op) refl (bridgeᶜ δ h M))
  bridgeᶜ δ h (delay τ M)               = delay τ (bridgeᶜ δ h M)
  bridgeᶜ {Γ = Γ} δ h (handle_`with_`in {B = B} M H N) =
    handle (bridgeᶜ δ h M)
      `with (λ op c → castᶜ (clause-ctx Γ δ op B c) (clause-ty Γ δ op B c)
                         (bridgeᶜ (δ ,ᵉ econst c) (⊩ᴴ-,ᵉ (econst c) h) (H op)))
      `in (bridgeᶜ δ h N)
  bridgeᶜ δ h (unbox x p q N)           =
    unbox var⌞ x ⌟ (inst-≾ᵣ h p) (inst-<:ᵛ h q) (bridgeᶜ δ h N)
  bridgeᶜ δ h (box ρ V N)               = box (bridgeᵛ δ h V) (bridgeᶜ δ h N)
  bridgeᶜ δ h (annᶜ C M)                = bridgeᶜ δ h M
  bridgeᶜ δ h (subC M p)                = subC (bridgeᶜ δ h M) (inst-<:ᶜ h p)

------------------------------------------------------------------------
-- The bridge keeps the term

mutual

  bridgeᵛ-⌊⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
             → (δ : Subst Θ ∅ˢ) → (h : ∅ᴴ ⊩ᴴ Q [ δ ])
             → (V : Q ∣ Γ ⊢V⦂ A)
             → CE.⌊ bridgeᵛ δ h V ⌋ᵛ ≡ ⌊ OE.⌊ V ⌋ᵛ ⌋ᴿᵛ
  bridgeᵛ-⌊⌋ δ h (var x ok)   = cong var (var⌞⌟-pos x)
  bridgeᵛ-⌊⌋ δ h (const B c)  = refl
  bridgeᵛ-⌊⌋ δ h ⋆            = refl
  bridgeᵛ-⌊⌋ δ h true         = refl
  bridgeᵛ-⌊⌋ δ h false        = refl
  bridgeᵛ-⌊⌋ δ h zero         = refl
  bridgeᵛ-⌊⌋ δ h (succ V)     = cong succ (bridgeᵛ-⌊⌋ δ h V)
  bridgeᵛ-⌊⌋ δ h ⦉ V , W ⦊     = cong₂ ⦉_,_⦊ (bridgeᵛ-⌊⌋ δ h V) (bridgeᵛ-⌊⌋ δ h W)
  bridgeᵛ-⌊⌋ δ h (inl V)      = cong inl (bridgeᵛ-⌊⌋ δ h V)
  bridgeᵛ-⌊⌋ δ h (inr V)      = cong inr (bridgeᵛ-⌊⌋ δ h V)
  bridgeᵛ-⌊⌋ δ h nil          = refl
  bridgeᵛ-⌊⌋ δ h (cons V W)   = cong₂ cons (bridgeᵛ-⌊⌋ δ h V) (bridgeᵛ-⌊⌋ δ h W)
  bridgeᵛ-⌊⌋ δ h (lam M)      = cong lam (bridgeᶜ-⌊⌋ δ h M)
  bridgeᵛ-⌊⌋ δ h (annᵛ A V)   = bridgeᵛ-⌊⌋ δ h V
  bridgeᵛ-⌊⌋ δ h (subV V p)   = bridgeᵛ-⌊⌋ δ h V

  -- the handler case compares clause families, functions of the operation
  -- and the continuation grade, and so uses `fun-ext`

  bridgeᶜ-⌊⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
             → (δ : Subst Θ ∅ˢ) → (h : ∅ᴴ ⊩ᴴ Q [ δ ])
             → (M : Q ∣ Γ ⊢C⦂ C)
             → CE.⌊ bridgeᶜ δ h M ⌋ᶜ ≡ ⌊ OE.⌊ M ⌋ᶜ ⌋ᴿᶜ
  bridgeᶜ-⌊⌋ δ h (return V)                = cong return (bridgeᵛ-⌊⌋ δ h V)
  bridgeᶜ-⌊⌋ δ h (M ⨟ N)                   = cong₂ _⨟_ (bridgeᶜ-⌊⌋ δ h M) (bridgeᶜ-⌊⌋ δ h N)
  bridgeᶜ-⌊⌋ δ h (V · W)                   = cong₂ _·_ (bridgeᵛ-⌊⌋ δ h V) (bridgeᵛ-⌊⌋ δ h W)
  bridgeᶜ-⌊⌋ δ h (match V `in M)           =
    cong₂ match_`in_ (bridgeᵛ-⌊⌋ δ h V) (bridgeᶜ-⌊⌋ δ h M)
  bridgeᶜ-⌊⌋ δ h (absurd V)                = cong absurd (bridgeᵛ-⌊⌋ δ h V)
  bridgeᶜ-⌊⌋ δ h (if V `then M `else N)    =
    cong₃ if_`then_`else_ (bridgeᵛ-⌊⌋ δ h V) (bridgeᶜ-⌊⌋ δ h M) (bridgeᶜ-⌊⌋ δ h N)
  bridgeᶜ-⌊⌋ δ h (cmp ⋈ V W et)            =
    cong₂ (cmp ⋈) (bridgeᵛ-⌊⌋ δ h V) (bridgeᵛ-⌊⌋ δ h W)
  bridgeᶜ-⌊⌋ δ h (caseℕ V `zero M `succ N) =
    cong₃ caseℕ_`zero_`succ_ (bridgeᵛ-⌊⌋ δ h V) (bridgeᶜ-⌊⌋ δ h M) (bridgeᶜ-⌊⌋ δ h N)
  bridgeᶜ-⌊⌋ δ h (case+ V `inl M `inr N)   =
    cong₃ case+_`inl_`inr_ (bridgeᵛ-⌊⌋ δ h V) (bridgeᶜ-⌊⌋ δ h M) (bridgeᶜ-⌊⌋ δ h N)
  bridgeᶜ-⌊⌋ δ h (caseL V `nil M `cons N)  =
    cong₃ caseL_`nil_`cons_ (bridgeᵛ-⌊⌋ δ h V) (bridgeᶜ-⌊⌋ δ h M) (bridgeᶜ-⌊⌋ δ h N)
  bridgeᶜ-⌊⌋ δ h (recℕ V M N p)            =
    cong₃ recℕ (bridgeᵛ-⌊⌋ δ h V) (bridgeᶜ-⌊⌋ δ h M) (bridgeᶜ-⌊⌋ δ h N)
  bridgeᶜ-⌊⌋ δ h (recL V M N p)            =
    cong₃ recL (bridgeᵛ-⌊⌋ δ h V) (bridgeᶜ-⌊⌋ δ h M) (bridgeᶜ-⌊⌋ δ h N)
  bridgeᶜ-⌊⌋ {Γ = Γ} δ h (perform op V M)  =
    cong₂ (perform op)
          (trans (castᵛ-⌊⌋ refl (⌞⌜ param op ⌝ᵍ⌟ δ) (bridgeᵛ δ h V)) (bridgeᵛ-⌊⌋ δ h V))
          (trans (castᶜ-⌊⌋ (perform-ctx Γ δ op) refl (bridgeᶜ δ h M)) (bridgeᶜ-⌊⌋ δ h M))
  bridgeᶜ-⌊⌋ δ h (delay τ M)               = cong (delay τ) (bridgeᶜ-⌊⌋ δ h M)
  bridgeᶜ-⌊⌋ {Γ = Γ} δ h (handle_`with_`in {B = B} M H N) =
    cong₃ (λ x y z → handle x `with y `in z)
          (bridgeᶜ-⌊⌋ δ h M)
          (fun-ext λ op → fun-ext λ c →
             trans (castᶜ-⌊⌋ (clause-ctx Γ δ op B c) (clause-ty Γ δ op B c)
                             (bridgeᶜ (δ ,ᵉ econst c) (⊩ᴴ-,ᵉ (econst c) h) (H op)))
                   (bridgeᶜ-⌊⌋ (δ ,ᵉ econst c) (⊩ᴴ-,ᵉ (econst c) h) (H op)))
          (bridgeᶜ-⌊⌋ δ h N)
  bridgeᶜ-⌊⌋ δ h (unbox x p q N)           =
    cong₂ unbox (var⌞⌟-pos x) (bridgeᶜ-⌊⌋ δ h N)
  bridgeᶜ-⌊⌋ δ h (box ρ V N)               = cong₂ box (bridgeᵛ-⌊⌋ δ h V) (bridgeᶜ-⌊⌋ δ h N)
  bridgeᶜ-⌊⌋ δ h (annᶜ C M)                = bridgeᶜ-⌊⌋ δ h M
  bridgeᶜ-⌊⌋ δ h (subC M p)                = bridgeᶜ-⌊⌋ δ h M

------------------------------------------------------------------------
-- The theorem: an open derivation at a closed instance satisfying its
-- hypotheses is a closed typing of the same term

bridge : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
       → (δ : Subst Θ ∅ˢ) → δ ⊨ Q ∣ []
       → (D : Q ∣ Γ ⊢C⦂ C)
       → Σ[ D' ∈ ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⊢C⦂ ⌞ C [ δ ]ᶜ ⌟ᶜ ] (CE.⌊ D' ⌋ᶜ ≡ ⌊ OE.⌊ D ⌋ᶜ ⌋ᴿᶜ)
bridge δ (h ∷ᴬ _) D = bridgeᶜ δ h D , bridgeᶜ-⌊⌋ δ h D
