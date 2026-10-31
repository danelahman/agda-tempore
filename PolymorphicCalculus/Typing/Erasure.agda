------------------------------------------------------------------
-- Erasure of open derivations to raw terms                     --
--                                                              --
-- `⌊_⌋ᵛ` and `⌊_⌋ᶜ` forget types and entailment premises and   --
-- keep what a raw term records: a variable becomes its         --
-- full-context position, a resource value its variable under   --
-- annotations, a definition its position. Subsumption erases   --
-- to its subject.                                              --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero)
open import Data.Nat using (ℕ)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Typing.Erasure (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades   S
open import PolymorphicCalculus.Syntax.Types    S
open import PolymorphicCalculus.Syntax.Contexts S
open import PolymorphicCalculus.Hypotheses      S
open import PolymorphicCalculus.Typing          S

open import PolymorphicCalculus.Syntax.Raw    S

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

  ⌊ var x p ⌋ᵛ    = var (var-pos x)
  ⌊ usedef {k = k} f δ h e ⌋ᵛ = usedef k
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

  ⌊ handler N H ⌋ᵛ = handler ⌊ N ⌋ᶜ (λ op → ⌊ H op ⌋ᶜ)
  ⌊ annᵛ A V ⌋ᵛ   = ⌊ V ⌋ᵛ ⦂ᵛ A
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

  ⌊ subC M p ⌋ᶜ                 = ⌊ M ⌋ᶜ

-- Sanity checks

private

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  ex-⋆ : ∅ᴴ ∣ (∅ᶜ ∷ Unit) ⊢V⦂ Unit
  ex-⋆ = ⋆

  ex-⋆-erase : ⌊ ex-⋆ ⌋ᵛ ≡ ⋆
  ex-⋆-erase = refl

  -- locks are forgotten, positions kept

  ex-var-lock : ∅ᴴ ∣ ((∅ᶜ ∷ Unit) ⟨ rconst 𝟏ᵣ ⟩) ⊢V⦂ Unit
  ex-var-lock = var (Tl-⟨⟩ Hd) (et-ok Unitₑ)

  ex-var-lock-erase : ⌊ ex-var-lock ⌋ᵛ ≡ var zero
  ex-var-lock-erase = refl

  ex-var-barrier : ∅ᴴ ∣ ((∅ᶜ ∷ Unit) ⟨ rconst ⊤ᵣ ⟩) ⊢V⦂ Unit
  ex-var-barrier = var (Tl-⟨⟩ Hd) (et-ok Unitₑ)

  ex-var-barrier-erase : ⌊ ex-var-barrier ⌋ᵛ ≡ var zero
  ex-var-barrier-erase = refl

  ex-unbox : ∅ᴴ ∣ (∅ᶜ ∷ [ 𝟏̂ᵣ ] Unit) ⊢C⦂ Unit ‼ 𝟏̂ₑ
  ex-unbox = unbox (res-var {z = Hd}) ⊩≾̂ᵣ-refl (return ⋆)

  ex-unbox-erase : ⌊ ex-unbox ⌋ᶜ ≡ unbox (var zero) (return ⋆)
  ex-unbox-erase = refl

  -- annotations are kept

  ex-unbox-ann : ∅ᴴ ∣ (∅ᶜ ∷ [ 𝟏̂ᵣ ] Unit) ⊢C⦂ Unit ‼ 𝟏̂ₑ
  ex-unbox-ann = unbox (res-ann 𝟏̂ᵣ Unit (res-var {z = Hd}) ⊩≾̂ᵣ-refl Unitₛ) ⊩≾̂ᵣ-refl (return ⋆)

  ex-unbox-ann-erase : ⌊ ex-unbox-ann ⌋ᶜ ≡ unbox (var zero ⦂ᵛ [ 𝟏̂ᵣ ] Unit) (return ⋆)
  ex-unbox-ann-erase = refl

  -- sub-effecting is invisible

  ex-coerce-erase : ⌊ coerce ⊩≾̂ₑ-refl ex-unbox ⌋ᶜ ≡ ⌊ ex-unbox ⌋ᶜ
  ex-coerce-erase = refl

  -- the grade of `box` is kept

  ex-box : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ [ 𝟏̂ᵣ ] Unit ‼ 𝟏̂ₑ
  ex-box = box 𝟏̂ᵣ ⋆ (return (var Hd (≾ᵘ-ok ⊩≾̂ᵣ-refl)))

  ex-box-erase : ⌊ ex-box ⌋ᶜ ≡ box 𝟏̂ᵣ ⋆ (return (var zero))
  ex-box-erase = refl
