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

⌊_⌋ʳ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ' : RExp Θ} {A : OVType Θ}
     → Q ⊢ A ∈̂[ ρ' ] Γ
     -----------------
     → RawV Θ n
⌊ res-var z ⌋ʳ           = var (var-pos z)
⌊ res-ann ρₐ Xₐ R _ _ ⌋ʳ = ⌊ R ⌋ʳ ⦂ᵛ [ ρₐ ] Xₐ

mutual

  ⌊_⌋ᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
       → Q ∣ Γ ⊢ᵛ⦂ A
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
  ⌊ fun M ⌋ᵛ      = fun ⌊ M ⌋ᶜ

  ⌊ handler N H ⌋ᵛ = handler ⌊ N ⌋ᶜ (λ op → ⌊ H op ⌋ᶜ)
  ⌊ annᵛ A V ⌋ᵛ   = ⌊ V ⌋ᵛ ⦂ᵛ A
  ⌊ subV V p ⌋ᵛ   = ⌊ V ⌋ᵛ


  ⌊_⌋ᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
       → Q ∣ Γ ⊢ᶜ⦂ C
       -------------
       → RawC Θ n

  ⌊ return V ⌋ᶜ                 = return ⌊ V ⌋ᵛ
  ⌊ M ⨟ N ⌋ᶜ                    = ⌊ M ⌋ᶜ ⨟ ⌊ N ⌋ᶜ
  ⌊ V · W ⌋ᶜ                    = ⌊ V ⌋ᵛ · ⌊ W ⌋ᵛ
  ⌊ match V `with M ⌋ᶜ          = match ⌊ V ⌋ᵛ `with ⌊ M ⌋ᶜ
  ⌊ absurd V ⌋ᶜ                 = absurd ⌊ V ⌋ᵛ
  ⌊ if V `then M `else N ⌋ᶜ     = if ⌊ V ⌋ᵛ `then ⌊ M ⌋ᶜ `else ⌊ N ⌋ᶜ
  ⌊ matchℕ V `zero M `succ N ⌋ᶜ = matchℕ ⌊ V ⌋ᵛ `zero ⌊ M ⌋ᶜ `succ ⌊ N ⌋ᶜ
  ⌊ match+ V `inl M `inr N ⌋ᶜ   = match+ ⌊ V ⌋ᵛ `inl ⌊ M ⌋ᶜ `inr ⌊ N ⌋ᶜ
  ⌊ recℕ V M N _ ⌋ᶜ             = recℕ ⌊ V ⌋ᵛ ⌊ M ⌋ᶜ ⌊ N ⌋ᶜ
  ⌊ matchL V `nil M `cons N ⌋ᶜ  = matchL ⌊ V ⌋ᵛ `nil ⌊ M ⌋ᶜ `cons ⌊ N ⌋ᶜ
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

  ex-⋆ : ∅ᴴ ∣ (∅ᶜ ∷ unit) ⊢ᵛ⦂ unit
  ex-⋆ = ⋆

  ex-⋆-erase : ⌊ ex-⋆ ⌋ᵛ ≡ ⋆
  ex-⋆-erase = refl

  -- modalities are forgotten, positions kept

  ex-var-⟨⟩ : ∅ᴴ ∣ ((∅ᶜ ∷ unit) ⟨ rconst 𝟏ᵣ ⟩) ⊢ᵛ⦂ unit
  ex-var-⟨⟩ = var (Tl-⟨⟩ Hd) (et-ok unitₑ)

  ex-var-⟨⟩-erase : ⌊ ex-var-⟨⟩ ⌋ᵛ ≡ var zero
  ex-var-⟨⟩-erase = refl

  ex-var-barrier : ∅ᴴ ∣ ((∅ᶜ ∷ unit) ⟨ rconst ⊤ᵣ ⟩) ⊢ᵛ⦂ unit
  ex-var-barrier = var (Tl-⟨⟩ Hd) (et-ok unitₑ)

  ex-var-barrier-erase : ⌊ ex-var-barrier ⌋ᵛ ≡ var zero
  ex-var-barrier-erase = refl

  ex-unbox : ∅ᴴ ∣ (∅ᶜ ∷ [ 𝟏̂ᵣ ] unit) ⊢ᶜ⦂ unit ! 𝟏̂ₑ
  ex-unbox = unbox (res-var Hd) ⊩≾̂ᵣ-refl (return ⋆)

  ex-unbox-erase : ⌊ ex-unbox ⌋ᶜ ≡ unbox (var zero) (return ⋆)
  ex-unbox-erase = refl

  -- annotations are kept

  ex-unbox-ann : ∅ᴴ ∣ (∅ᶜ ∷ [ 𝟏̂ᵣ ] unit) ⊢ᶜ⦂ unit ! 𝟏̂ₑ
  ex-unbox-ann = unbox (res-ann 𝟏̂ᵣ unit (res-var Hd) ⊩≾̂ᵣ-refl unitₛ) ⊩≾̂ᵣ-refl (return ⋆)

  ex-unbox-ann-erase : ⌊ ex-unbox-ann ⌋ᶜ ≡ unbox (var zero ⦂ᵛ [ 𝟏̂ᵣ ] unit) (return ⋆)
  ex-unbox-ann-erase = refl

  -- sub-effecting is invisible

  ex-coerce-erase : ⌊ coerce ⊩≾̂ₑ-refl ex-unbox ⌋ᶜ ≡ ⌊ ex-unbox ⌋ᶜ
  ex-coerce-erase = refl

  -- the grade of `box` is kept

  ex-box : ∅ᴴ ∣ ∅ᶜ ⊢ᶜ⦂ [ 𝟏̂ᵣ ] unit ! 𝟏̂ₑ
  ex-box = box 𝟏̂ᵣ ⋆ (return (var Hd (≾ᵘ-ok ⊩≾̂ᵣ-refl)))

  ex-box-erase : ⌊ ex-box ⌋ᶜ ≡ box 𝟏̂ᵣ ⋆ (return (var zero))
  ex-box-erase = refl
