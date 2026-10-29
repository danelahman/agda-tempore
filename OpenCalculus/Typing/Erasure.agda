------------------------------------------------------------------
-- Erasure of open derivations to raw terms                     --
--                                                              --
-- `⌊_⌋ᵛ` and `⌊_⌋ᶜ` map the well-typed syntax of               --
-- `OpenCalculus.Typing` to the well-scoped raw                 --
-- syntax of `OpenCalculus.Syntax.Raw`, forgetting types and    --
-- entailment premises and keeping the data a raw term records. --
--                                                              --
-- Erasure is index-preserving: a derivation over `Θ` erases to --
-- a raw term over `Θ`, a handler clause to a                   --
-- `RawC (Θ +e) (2+n)`, a variable to its full-context          --
-- position `var-pos`, a resource value to that of its variable --
-- under its annotations (`⌊_⌋ʳ`), and a definition to its      --
-- position in the program context. It is not injective: `subV` --
-- and `subC` erase to their subjects. The annotation rules     --
-- `annᵛ` and `annᶜ` erase to the annotated raw forms.          --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero)
open import Data.Nat using (ℕ)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Typing.Erasure (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OpenCalculus.Syntax.Grades   S
open import OpenCalculus.Syntax.Types    S
open import OpenCalculus.Syntax.Contexts S
open import OpenCalculus.Hypotheses      S
open import OpenCalculus.Typing          S

open import OpenCalculus.Syntax.Raw    S

-- A resource value erases to its variable under its annotations

⌊_⌋ʳ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ' ρ₀ ρ : RExp Θ} {X₀ X : OVType Θ}
       {z : [ ρ₀ ] X₀ ∈̂[ ρ' ] Γ}
     → Q ∣ Γ ⊢↪[ ρ' ] z ⦂[ ρ ] X
     ---------------------------
     → RawV Θ n
⌊_⌋ʳ {z = z} res-var    = var (var-pos z)
⌊ res-ann ρₐ Xₐ R _ _ ⌋ʳ = ⌊ R ⌋ʳ ⦂ᵛ [ ρₐ ] Xₐ

mutual

  ⌊_⌋ᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
       → Q ∣ Γ ⊢V⦂ A
       -------------
       → RawV Θ n

  -- the raw index of a variable is its full-context position

  ⌊ var x p ⌋ᵛ    = var (var-pos x)
  ⌊ def {k = k} f δ h e ⌋ᵛ = def k
  ⌊ const B c ⌋ᵛ  = const B c
  ⌊ ⋆ ⌋ᵛ          = ⋆
  ⌊ true ⌋ᵛ       = true
  ⌊ false ⌋ᵛ      = false
  ⌊ zero ⌋ᵛ       = zero
  ⌊ succ V ⌋ᵛ     = succ ⌊ V ⌋ᵛ
  ⌊ inl V ⌋ᵛ      = inl ⌊ V ⌋ᵛ
  ⌊ inr V ⌋ᵛ      = inr ⌊ V ⌋ᵛ
  ⌊ nil ⌋ᵛ        = nil
  ⌊ cons V W ⌋ᵛ   = cons ⌊ V ⌋ᵛ ⌊ W ⌋ᵛ
  ⌊ cmp ⋈ V W _ ⌋ᵛ = cmp ⋈ ⌊ V ⌋ᵛ ⌊ W ⌋ᵛ
  ⌊ ⦉ V , W ⦊ ⌋ᵛ   = ⦉ ⌊ V ⌋ᵛ , ⌊ W ⌋ᵛ ⦊
  ⌊ lam M ⌋ᵛ      = lam ⌊ M ⌋ᶜ

  -- the clause family is erased pointwise; `H op` is typed at `Θ +e` over a
  -- context of arity `2 + n`, which is the raw clause's scope on the nose

  ⌊ handler N H ⌋ᵛ = handler ⌊ N ⌋ᶜ (λ op → ⌊ H op ⌋ᶜ)
  ⌊ annᵛ A V ⌋ᵛ   = ⌊ V ⌋ᵛ ⦂ᵛ A

  -- subsumption is invisible

  ⌊ subV V p ⌋ᵛ   = ⌊ V ⌋ᵛ


  ⌊_⌋ᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
       → Q ∣ Γ ⊢C⦂ C
       -------------
       → RawC Θ n

  ⌊ return V ⌋ᶜ                 = return ⌊ V ⌋ᵛ
  ⌊ M ⨟ N ⌋ᶜ                    = ⌊ M ⌋ᶜ ⨟ ⌊ N ⌋ᶜ
  ⌊ V · W ⌋ᶜ                    = ⌊ V ⌋ᵛ · ⌊ W ⌋ᵛ
  ⌊ match V `in M ⌋ᶜ            = match ⌊ V ⌋ᵛ `in ⌊ M ⌋ᶜ
  ⌊ absurd V ⌋ᶜ                 = absurd ⌊ V ⌋ᵛ
  ⌊ if V `then M `else N ⌋ᶜ     = if ⌊ V ⌋ᵛ `then ⌊ M ⌋ᶜ `else ⌊ N ⌋ᶜ
  ⌊ caseℕ V `zero M `succ N ⌋ᶜ  = caseℕ ⌊ V ⌋ᵛ `zero ⌊ M ⌋ᶜ `succ ⌊ N ⌋ᶜ
  ⌊ case+ V `inl M `inr N ⌋ᶜ    = case+ ⌊ V ⌋ᵛ `inl ⌊ M ⌋ᶜ `inr ⌊ N ⌋ᶜ
  ⌊ recℕ V M N _ ⌋ᶜ             = recℕ ⌊ V ⌋ᵛ ⌊ M ⌋ᶜ ⌊ N ⌋ᶜ
  ⌊ caseL V `nil M `cons N ⌋ᶜ   = caseL ⌊ V ⌋ᵛ `nil ⌊ M ⌋ᶜ `cons ⌊ N ⌋ᶜ
  ⌊ recL V M N _ ⌋ᶜ             = recL ⌊ V ⌋ᵛ ⌊ M ⌋ᶜ ⌊ N ⌋ᶜ
  ⌊ perform op V M ⌋ᶜ           = perform op ⌊ V ⌋ᵛ ⌊ M ⌋ᶜ
  ⌊ delay τ M ⌋ᶜ                = delay τ ⌊ M ⌋ᶜ

  ⌊ handle M `with V ⌋ᶜ         = handle ⌊ M ⌋ᶜ `with ⌊ V ⌋ᵛ

  ⌊ unbox R p N ⌋ᶜ              = unbox ⌊ R ⌋ʳ ⌊ N ⌋ᶜ

  ⌊ box ρ V N ⌋ᶜ                = box ρ ⌊ V ⌋ᵛ ⌊ N ⌋ᶜ

  ⌊ annᶜ C M ⌋ᶜ                 = ⌊ M ⌋ᶜ ⦂ᶜ C

  -- subsumption is invisible

  ⌊ subC M p ⌋ᶜ                 = ⌊ M ⌋ᶜ

-- Sanity checks: erasure computes as intended.

-- The scope has to be given explicitly, as in
-- `OpenCalculus.Typing`: `OCtx`'s scope is not
-- determined by `[]`.

private

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  -- a value in a plain context

  ex-⋆ : ∅ᴴ ∣ (∅ᶜ ∷ Unit) ⊢V⦂ Unit
  ex-⋆ = ⋆

  ex-⋆-erase : ⌊ ex-⋆ ⌋ᵛ ≡ ⋆
  ex-⋆-erase = refl

  -- a variable used after time-passage: the lock is forgotten, the position kept

  ex-var-lock : ∅ᴴ ∣ ((∅ᶜ ∷ Unit) ⟨ rconst uᵣ ⟩) ⊢V⦂ Unit
  ex-var-lock = var (Tl-⟨⟩ Hd) (et-ok Unitₑ)

  ex-var-lock-erase : ⌊ ex-var-lock ⌋ᵛ ≡ var zero
  ex-var-lock-erase = refl

  -- a variable used across a clause barrier: that lock too is forgotten

  ex-var-barrier : ∅ᴴ ∣ ((∅ᶜ ∷ Unit) ⟨ rconst ⊤ᵣ ⟩) ⊢V⦂ Unit
  ex-var-barrier = var (Tl-⟨⟩ Hd) (et-ok Unitₑ)

  ex-var-barrier-erase : ⌊ ex-var-barrier ⌋ᵛ ≡ var zero
  ex-var-barrier-erase = refl

  -- unboxing a boxed variable

  ex-unbox : ∅ᴴ ∣ (∅ᶜ ∷ [ ûᵣ ] Unit) ⊢C⦂ Unit ‼ ûₑ
  ex-unbox = unbox (res-var {z = Hd}) ⊩≾̂ᵣ-refl (return ⋆)

  ex-unbox-erase : ⌊ ex-unbox ⌋ᶜ ≡ unbox (var zero) (return ⋆)
  ex-unbox-erase = refl

  -- unboxing an annotated variable: the annotation is kept

  ex-unbox-ann : ∅ᴴ ∣ (∅ᶜ ∷ [ ûᵣ ] Unit) ⊢C⦂ Unit ‼ ûₑ
  ex-unbox-ann = unbox (res-ann ûᵣ Unit (res-var {z = Hd}) ⊩≾̂ᵣ-refl Unitₛ) ⊩≾̂ᵣ-refl (return ⋆)

  ex-unbox-ann-erase : ⌊ ex-unbox-ann ⌋ᶜ ≡ unbox (var zero ⦂ᵛ [ ûᵣ ] Unit) (return ⋆)
  ex-unbox-ann-erase = refl

  -- coerce-invisibility: a sub-effecting step leaves the raw term untouched

  ex-coerce-erase : ⌊ coerce ⊩≾̂ₑ-refl ex-unbox ⌋ᶜ ≡ ⌊ ex-unbox ⌋ᶜ
  ex-coerce-erase = refl

  -- boxing a value: the grade is kept

  ex-box : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ [ ûᵣ ] Unit ‼ ûₑ
  ex-box = box ûᵣ ⋆ (return (var Hd (≾ᵘ-ok ⊩≾̂ᵣ-refl)))

  ex-box-erase : ⌊ ex-box ⌋ᶜ ≡ box ûᵣ ⋆ (return (var zero))
  ex-box-erase = refl
