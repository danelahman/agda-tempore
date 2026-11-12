------------------------------------------------------------------
-- Soundness of constraint generation                           --
--                                                              --
-- A solution of a generated constraint elaborates to a         --
-- derivation of the polymorphic calculus erasing to the raw    --
-- term, its annotations instantiated by the solution           --
-- (`soundV`, `soundC`).                                        --
------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe.Base using (just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.Soundness (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades              S
open import PolymorphicCalculus.Syntax.Types               S
open import PolymorphicCalculus.Syntax.Contexts            S
open import PolymorphicCalculus.Syntax.Contexts.Properties S
open import PolymorphicCalculus.Syntax.GradeSubstitution   S
open import PolymorphicCalculus.Hypotheses                 S
open import PolymorphicCalculus.Typing                     S

open import PolymorphicCalculus.Syntax.Raw                   S
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S
open import PolymorphicCalculus.Typing.Erasure               S
open import PolymorphicCalculus.Typing.Conversion S using (equivalence; conv-last)

open import PolymorphicCalculus.Inference.Constraints.Syntax       S
open import PolymorphicCalculus.Inference.Constraints.Satisfaction S
open import PolymorphicCalculus.Inference.Constraints.Schemes      S using (instᶜ-sound)

open import PolymorphicCalculus.Inference.Generate S

-- The typing judgement transports annotations only; handler clause contexts,
-- and contexts built under a generation binder, need the context transported too.

ctx-substᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ Γ' : OCtx Θ n} {A : OVType Θ}
           → Γ ≡ Γ'
           → Q ∣ Γ  ⊢ᵛ⦂ A
           ---------------
           → Q ∣ Γ' ⊢ᵛ⦂ A

ctx-substᵛ refl V = V

ctx-substᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ Γ' : OCtx Θ n} {C : OCType Θ}
           → Γ ≡ Γ'
           → Q ∣ Γ  ⊢ᶜ⦂ C
           ---------------
           → Q ∣ Γ' ⊢ᶜ⦂ C

ctx-substᶜ refl M = M

⌊ty⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A A' : OVType Θ}
     → (e : A ≡ A') → (V : Q ∣ Γ ⊢ᵛ⦂ A) → ⌊ ty-subst e V ⌋ᵛ ≡ ⌊ V ⌋ᵛ
⌊ty⌋ refl V = refl

⌊c⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C C' : OCType Θ}
    → (e : C ≡ C') → (M : Q ∣ Γ ⊢ᶜ⦂ C) → ⌊ c-subst e M ⌋ᶜ ≡ ⌊ M ⌋ᶜ
⌊c⌋ refl M = refl

⌊ctxᵛ⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ Γ' : OCtx Θ n} {A : OVType Θ}
       → (e : Γ ≡ Γ') → (V : Q ∣ Γ ⊢ᵛ⦂ A) → ⌊ ctx-substᵛ e V ⌋ᵛ ≡ ⌊ V ⌋ᵛ
⌊ctxᵛ⌋ refl V = refl

⌊ctxᶜ⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ Γ' : OCtx Θ n} {C : OCType Θ}
       → (e : Γ ≡ Γ') → (M : Q ∣ Γ ⊢ᶜ⦂ C) → ⌊ ctx-substᶜ e M ⌋ᶜ ≡ ⌊ M ⌋ᶜ
⌊ctxᶜ⌋ refl M = refl

-- Generation weakens into the scope of its `∃`s and satisfaction extends `σ`;
-- each pair cancels (`wk-,*`), one lemma per binder pattern, `wk-,ᵗ-*` for one `∃ᵗ`.

-- `∃ᵗ∃ᵗ`: pairing, injections, pattern-matching, sum elimination

co²ᵗ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ') → (Γ : OCtx Θ n)
         → wkᵗ-ctx (wkᵗ-ctx Γ) [ σ ,ᵗ B₁ ,ᵗ B₂ ]ᶜᵗˣ ≡ Γ [ σ ]ᶜᵗˣ
co²ᵗ-ctx σ B₁ B₂ Γ = trans (wk-,ᵗ-ctx (σ ,ᵗ B₁) B₂ (wkᵗ-ctx Γ)) (wk-,ᵗ-ctx σ B₁ Γ)

co²ᵗ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ') → (A : OVType Θ)
       → wkᵗ-v (wkᵗ-v A) [ σ ,ᵗ B₁ ,ᵗ B₂ ]ᵛ ≡ A [ σ ]ᵛ
co²ᵗ-v σ B₁ B₂ A = trans (wk-,ᵗ-v (σ ,ᵗ B₁) B₂ (wkᵗ-v A)) (wk-,ᵗ-v σ B₁ A)

co²ᵗ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ') → (ε : EExp Θ)
       → wkᵗ-e (wkᵗ-e ε) [ σ ,ᵗ B₁ ,ᵗ B₂ ]ᵉ ≡ ε [ σ ]ᵉ
co²ᵗ-e σ B₁ B₂ ε = trans (wk-,ᵗ-e (σ ,ᵗ B₁) B₂ (wkᵗ-e ε)) (wk-,ᵗ-e σ B₁ ε)

co²ᵗ-r : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ') → (ρ : RExp Θ)
       → wkᵗ-r (wkᵗ-r ρ) [ σ ,ᵗ B₁ ,ᵗ B₂ ]ʳ ≡ ρ [ σ ]ʳ
co²ᵗ-r σ B₁ B₂ ρ = trans (wk-,ᵗ-r (σ ,ᵗ B₁) B₂ (wkᵗ-r ρ)) (wk-,ᵗ-r σ B₁ ρ)

-- `∃ᵗ∃ᵗ∃ᵉ`: lambda abstraction, function application, list recursion

co²ᵗᵉ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ') → (ε : EExp Θ')
          → (Γ : OCtx Θ n)
          → wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ)) [ σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε ]ᶜᵗˣ ≡ Γ [ σ ]ᶜᵗˣ
co²ᵗᵉ-ctx σ B₁ B₂ ε Γ =
  trans (wk-,ᵉ-ctx (σ ,ᵗ B₁ ,ᵗ B₂) ε (wkᵗ-ctx (wkᵗ-ctx Γ))) (co²ᵗ-ctx σ B₁ B₂ Γ)

co²ᵗᵉ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ') → (ε : EExp Θ')
        → (A : OVType Θ)
        → wkᵉ-v (wkᵗ-v (wkᵗ-v A)) [ σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε ]ᵛ ≡ A [ σ ]ᵛ
co²ᵗᵉ-v σ B₁ B₂ ε A =
  trans (wk-,ᵉ-v (σ ,ᵗ B₁ ,ᵗ B₂) ε (wkᵗ-v (wkᵗ-v A))) (co²ᵗ-v σ B₁ B₂ A)

co²ᵗᵉ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ') → (ε : EExp Θ')
        → (ε₀ : EExp Θ)
        → wkᵉ-e (wkᵗ-e (wkᵗ-e ε₀)) [ σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε ]ᵉ ≡ ε₀ [ σ ]ᵉ
co²ᵗᵉ-e σ B₁ B₂ ε ε₀ =
  trans (wk-,ᵉ-e (σ ,ᵗ B₁ ,ᵗ B₂) ε (wkᵗ-e (wkᵗ-e ε₀))) (co²ᵗ-e σ B₁ B₂ ε₀)

-- `∃ᵗ∃ʳ`: unboxing

coᵗʳ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (B : OVType Θ') → (ρ : RExp Θ')
         → (Γ : OCtx Θ n)
         → wkʳ-ctx (wkᵗ-ctx Γ) [ σ ,ᵗ B ,ʳ ρ ]ᶜᵗˣ ≡ Γ [ σ ]ᶜᵗˣ
coᵗʳ-ctx σ B ρ Γ = trans (wk-,ʳ-ctx (σ ,ᵗ B) ρ (wkᵗ-ctx Γ)) (wk-,ᵗ-ctx σ B Γ)

coᵗʳ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ') → (ρ : RExp Θ')
       → (A : OVType Θ)
       → wkʳ-v (wkᵗ-v A) [ σ ,ᵗ B ,ʳ ρ ]ᵛ ≡ A [ σ ]ᵛ
coᵗʳ-v σ B ρ A = trans (wk-,ʳ-v (σ ,ᵗ B) ρ (wkᵗ-v A)) (wk-,ᵗ-v σ B A)

coᵗʳ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ') → (ρ : RExp Θ')
       → (ε : EExp Θ)
       → wkʳ-e (wkᵗ-e ε) [ σ ,ᵗ B ,ʳ ρ ]ᵉ ≡ ε [ σ ]ᵉ
coᵗʳ-e σ B ρ ε = trans (wk-,ʳ-e (σ ,ᵗ B) ρ (wkᵗ-e ε)) (wk-,ᵗ-e σ B ε)

-- `∃ᵗ∃ᵉ`: a prefix of the `∃ᵗ∃ᵉ∃ᵉ` pattern below

coᵗᵉ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (B : OVType Θ') → (ε : EExp Θ')
         → (Γ : OCtx Θ n)
         → wkᵉ-ctx (wkᵗ-ctx Γ) [ σ ,ᵗ B ,ᵉ ε ]ᶜᵗˣ ≡ Γ [ σ ]ᶜᵗˣ
coᵗᵉ-ctx σ B ε Γ = trans (wk-,ᵉ-ctx (σ ,ᵗ B) ε (wkᵗ-ctx Γ)) (wk-,ᵗ-ctx σ B Γ)

coᵗᵉ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ') → (ε : EExp Θ')
       → (A : OVType Θ)
       → wkᵉ-v (wkᵗ-v A) [ σ ,ᵗ B ,ᵉ ε ]ᵛ ≡ A [ σ ]ᵛ
coᵗᵉ-v σ B ε A = trans (wk-,ᵉ-v (σ ,ᵗ B) ε (wkᵗ-v A)) (wk-,ᵗ-v σ B A)

coᵗᵉ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ') → (ε : EExp Θ')
       → (ε₀ : EExp Θ)
       → wkᵉ-e (wkᵗ-e ε₀) [ σ ,ᵗ B ,ᵉ ε ]ᵉ ≡ ε₀ [ σ ]ᵉ
coᵗᵉ-e σ B ε ε₀ = trans (wk-,ᵉ-e (σ ,ᵗ B) ε (wkᵗ-e ε₀)) (wk-,ᵗ-e σ B ε₀)

-- `∃ᵗ∃ᵉ∃ᵉ`: sequencing

coᵗ²ᵉ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (B : OVType Θ') → (ε₁ ε₂ : EExp Θ')
          → (Γ : OCtx Θ n)
          → wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx Γ)) [ σ ,ᵗ B ,ᵉ ε₁ ,ᵉ ε₂ ]ᶜᵗˣ ≡ Γ [ σ ]ᶜᵗˣ
coᵗ²ᵉ-ctx σ B ε₁ ε₂ Γ =
  trans (wk-,ᵉ-ctx (σ ,ᵗ B ,ᵉ ε₁) ε₂ (wkᵉ-ctx (wkᵗ-ctx Γ))) (coᵗᵉ-ctx σ B ε₁ Γ)

coᵗ²ᵉ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ') → (ε₁ ε₂ : EExp Θ')
        → (A : OVType Θ)
        → wkᵉ-v (wkᵉ-v (wkᵗ-v A)) [ σ ,ᵗ B ,ᵉ ε₁ ,ᵉ ε₂ ]ᵛ ≡ A [ σ ]ᵛ
coᵗ²ᵉ-v σ B ε₁ ε₂ A =
  trans (wk-,ᵉ-v (σ ,ᵗ B ,ᵉ ε₁) ε₂ (wkᵉ-v (wkᵗ-v A))) (coᵗᵉ-v σ B ε₁ A)

coᵗ²ᵉ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ') → (ε₁ ε₂ : EExp Θ')
        → (ε₀ : EExp Θ)
        → wkᵉ-e (wkᵉ-e (wkᵗ-e ε₀)) [ σ ,ᵗ B ,ᵉ ε₁ ,ᵉ ε₂ ]ᵉ ≡ ε₀ [ σ ]ᵉ
coᵗ²ᵉ-e σ B ε₁ ε₂ ε₀ =
  trans (wk-,ᵉ-e (σ ,ᵗ B ,ᵉ ε₁) ε₂ (wkᵉ-e (wkᵗ-e ε₀))) (coᵗᵉ-e σ B ε₁ ε₀)

-- the same, one `∀ᵉ` deeper: a handler clause

coᵗ²ᵉ-ctx↑ : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (B : OVType Θ') → (ε₁ ε₂ : EExp Θ')
           → (Γ : OCtx Θ n)
           → wkᵉ-ctx (wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx Γ))) [ (σ ,ᵗ B ,ᵉ ε₁ ,ᵉ ε₂) ↑ᵉ ]ᶜᵗˣ
             ≡ wkᵉ-ctx (Γ [ σ ]ᶜᵗˣ)
coᵗ²ᵉ-ctx↑ σ B ε₁ ε₂ Γ =
  trans (wk-↑ᵉ-ctx (σ ,ᵗ B ,ᵉ ε₁ ,ᵉ ε₂) (wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx Γ))))
        (cong wkᵉ-ctx (coᵗ²ᵉ-ctx σ B ε₁ ε₂ Γ))

coᵗ²ᵉ-v↑ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ') → (ε₁ ε₂ : EExp Θ')
         → (A : OVType Θ)
         → wkᵉ-v (wkᵉ-v (wkᵉ-v (wkᵗ-v A))) [ (σ ,ᵗ B ,ᵉ ε₁ ,ᵉ ε₂) ↑ᵉ ]ᵛ
           ≡ wkᵉ-v (A [ σ ]ᵛ)
coᵗ²ᵉ-v↑ σ B ε₁ ε₂ A =
  trans (wk-↑ᵉ-v (σ ,ᵗ B ,ᵉ ε₁ ,ᵉ ε₂) (wkᵉ-v (wkᵉ-v (wkᵗ-v A))))
        (cong wkᵉ-v (coᵗ²ᵉ-v σ B ε₁ ε₂ A))

-- `∃ᵗ∃ᵗ∃ᵉ∃ᵉ`: handlers, handling

co²ᵗ²ᵉ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ')
           → (ε₁ ε₂ : EExp Θ') → (Γ : OCtx Θ n)
           → wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ)))
               [ σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε₁ ,ᵉ ε₂ ]ᶜᵗˣ
             ≡ Γ [ σ ]ᶜᵗˣ
co²ᵗ²ᵉ-ctx σ B₁ B₂ ε₁ ε₂ Γ =
  trans (wk-,ᵉ-ctx (σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε₁) ε₂ (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))))
        (co²ᵗᵉ-ctx σ B₁ B₂ ε₁ Γ)

co²ᵗ²ᵉ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ')
         → (ε₁ ε₂ : EExp Θ') → (A : OVType Θ)
         → wkᵉ-v (wkᵉ-v (wkᵗ-v (wkᵗ-v A))) [ σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε₁ ,ᵉ ε₂ ]ᵛ ≡ A [ σ ]ᵛ
co²ᵗ²ᵉ-v σ B₁ B₂ ε₁ ε₂ A =
  trans (wk-,ᵉ-v (σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε₁) ε₂ (wkᵉ-v (wkᵗ-v (wkᵗ-v A))))
        (co²ᵗᵉ-v σ B₁ B₂ ε₁ A)

co²ᵗ²ᵉ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ')
         → (ε₁ ε₂ : EExp Θ') → (ε₀ : EExp Θ)
         → wkᵉ-e (wkᵉ-e (wkᵗ-e (wkᵗ-e ε₀))) [ σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε₁ ,ᵉ ε₂ ]ᵉ ≡ ε₀ [ σ ]ᵉ
co²ᵗ²ᵉ-e σ B₁ B₂ ε₁ ε₂ ε₀ =
  trans (wk-,ᵉ-e (σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε₁) ε₂ (wkᵉ-e (wkᵗ-e (wkᵗ-e ε₀))))
        (co²ᵗᵉ-e σ B₁ B₂ ε₁ ε₀)

-- the same, one `∀ᵉ` deeper: a handler clause

co²ᵗ²ᵉ-ctx↑ : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ')
            → (ε₁ ε₂ : EExp Θ') → (Γ : OCtx Θ n)
            → wkᵉ-ctx (wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))))
                [ (σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε₁ ,ᵉ ε₂) ↑ᵉ ]ᶜᵗˣ
              ≡ wkᵉ-ctx (Γ [ σ ]ᶜᵗˣ)
co²ᵗ²ᵉ-ctx↑ σ B₁ B₂ ε₁ ε₂ Γ =
  trans (wk-↑ᵉ-ctx (σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε₁ ,ᵉ ε₂)
                   (wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ)))))
        (cong wkᵉ-ctx (co²ᵗ²ᵉ-ctx σ B₁ B₂ ε₁ ε₂ Γ))

-- The raw term's interpretation, weakened under the binders and composed with
-- the extended solution, is the interpretation composed with the solution.

co²ᵗ-ˢ : ∀ {Θ₀ Θ Θ'} → (ι : Subst Θ₀ Θ) → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ')
       → (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ) ⨟ˢ (σ ,ᵗ B₁ ,ᵗ B₂) ≐ˢ ι ⨟ˢ σ
co²ᵗ-ˢ ι σ B₁ B₂ = ≐ˢ-trans (wk-,ᵗ-ˢ (ι ⨟ˢ wkˢᵗ) (σ ,ᵗ B₁) B₂) (wk-,ᵗ-ˢ ι σ B₁)

co²ᵗᵉ-ˢ : ∀ {Θ₀ Θ Θ'} → (ι : Subst Θ₀ Θ) → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ')
        → (ε : EExp Θ')
        → (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ) ⨟ˢ (σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε) ≐ˢ ι ⨟ˢ σ
co²ᵗᵉ-ˢ ι σ B₁ B₂ ε =
  ≐ˢ-trans (wk-,ᵉ-ˢ (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ) (σ ,ᵗ B₁ ,ᵗ B₂) ε) (co²ᵗ-ˢ ι σ B₁ B₂)

coᵗʳ-ˢ : ∀ {Θ₀ Θ Θ'} → (ι : Subst Θ₀ Θ) → (σ : Subst Θ Θ') → (B : OVType Θ')
       → (ρ : RExp Θ')
       → (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢʳ) ⨟ˢ (σ ,ᵗ B ,ʳ ρ) ≐ˢ ι ⨟ˢ σ
coᵗʳ-ˢ ι σ B ρ = ≐ˢ-trans (wk-,ʳ-ˢ (ι ⨟ˢ wkˢᵗ) (σ ,ᵗ B) ρ) (wk-,ᵗ-ˢ ι σ B)

coᵗᵉ-ˢ : ∀ {Θ₀ Θ Θ'} → (ι : Subst Θ₀ Θ) → (σ : Subst Θ Θ') → (B : OVType Θ')
       → (ε : EExp Θ')
       → (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ) ⨟ˢ (σ ,ᵗ B ,ᵉ ε) ≐ˢ ι ⨟ˢ σ
coᵗᵉ-ˢ ι σ B ε = ≐ˢ-trans (wk-,ᵉ-ˢ (ι ⨟ˢ wkˢᵗ) (σ ,ᵗ B) ε) (wk-,ᵗ-ˢ ι σ B)

coᵗ²ᵉ-ˢ : ∀ {Θ₀ Θ Θ'} → (ι : Subst Θ₀ Θ) → (σ : Subst Θ Θ') → (B : OVType Θ')
        → (ε₁ ε₂ : EExp Θ')
        → (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ) ⨟ˢ (σ ,ᵗ B ,ᵉ ε₁ ,ᵉ ε₂) ≐ˢ ι ⨟ˢ σ
coᵗ²ᵉ-ˢ ι σ B ε₁ ε₂ =
  ≐ˢ-trans (wk-,ᵉ-ˢ (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ) (σ ,ᵗ B ,ᵉ ε₁) ε₂)
           (≐ˢ-trans (wk-,ᵉ-ˢ (ι ⨟ˢ wkˢᵗ) (σ ,ᵗ B) ε₁) (wk-,ᵗ-ˢ ι σ B))

co²ᵗ²ᵉ-ˢ : ∀ {Θ₀ Θ Θ'} → (ι : Subst Θ₀ Θ) → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ')
         → (ε₁ ε₂ : EExp Θ')
         → (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ) ⨟ˢ (σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε₁ ,ᵉ ε₂)
           ≐ˢ ι ⨟ˢ σ
co²ᵗ²ᵉ-ˢ ι σ B₁ B₂ ε₁ ε₂ =
  ≐ˢ-trans (wk-,ᵉ-ˢ (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ) (σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε₁) ε₂)
           (co²ᵗᵉ-ˢ ι σ B₁ B₂ ε₁)

-- the same, one `∀ᵉ` deeper: a handler clause

co²ᵗ²ᵉ-ˢ↑ : ∀ {Θ₀ Θ Θ'} → (ι : Subst Θ₀ Θ) → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ')
          → (ε₁ ε₂ : EExp Θ')
          → ((ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ) ↑ᵉ)
              ⨟ˢ ((σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε₁ ,ᵉ ε₂) ↑ᵉ)
            ≐ˢ (ι ⨟ˢ σ) ↑ᵉ
co²ᵗ²ᵉ-ˢ↑ ι σ B₁ B₂ ε₁ ε₂ =
  ≐ˢ-trans (⨟-↑ᵉ (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ) (σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε₁ ,ᵉ ε₂))
           (≐ˢ-↑ᵉ (co²ᵗ²ᵉ-ˢ ι σ B₁ B₂ ε₁ ε₂))

-- A use of a definition: the position is bound to a scheme the substituted
-- context keeps, its instance solving the constraint

soundUseDef : ∀ {Θ n Θ'} → (σ : Subst Θ Θ') → {Q : Hyps Θ'}
            → (Γ : OCtx Θ n) → (k : ℕ) → (A : OVType Θ)
            → σ ⊨[ Q ] useDefConstraint (lookupᵖ (defs Γ) k) A
            → Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢ᵛ⦂ A [ σ ]ᵛ) ] (⌊ D ⌋ᵛ ≡ usedef k)
soundUseDef σ Γ k A s with lookupᵖ (defs Γ) k in eq
... | nothing = ⊥-elim s
... | just sc with instᶜ-sound sc A s
...   | δ , st , h =
  subV (usedef (subst (sc ∈ᵖ[ k ]_) (sym (defs-subst Γ σ)) (lookupᵖ-∈ (defs Γ) eq)) δ h refl) st , refl

-- A resource value: its constraint, where the type reached is a box type, gives
-- a resource value reaching it, the variable's witness being `lookup-var`

private

  mem-cast : ∀ {Θ n} {A A' : OVType Θ} {ρ ρ' : RExp Θ} {Γ : OCtx Θ n}
           → A ≡ A' → ρ ≡ ρ' → A ∈̂[ ρ ] Γ → A' ∈̂[ ρ' ] Γ
  mem-cast refl refl x = x

  var-pos-cast : ∀ {Θ n} {A A' : OVType Θ} {ρ ρ' : RExp Θ} {Γ : OCtx Θ n}
               → (e : A ≡ A') → (e' : ρ ≡ ρ') → (x : A ∈̂[ ρ ] Γ)
               → var-pos (mem-cast e e' x) ≡ var-pos x
  var-pos-cast refl refl x = refl

soundR : ∀ {Θ₀ Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {Γ₀ : OCtx Θ' n}
       → (ι : Subst Θ₀ Θ) → (Γ : OCtx Θ n) → (V : RawV Θ₀ n)
       → Γ [ σ ]ᶜᵗˣ ≡ Γ₀
       → σ ⊨[ Q ] resC ι Γ V
       → {ρ : RExp Θ'} {X : OVType Θ'} → resTy ι Γ V [ σ ]ᵛ ≡ [ ρ ] X
       --------------------------------------------------------------------
       → Σ[ R ∈ Q ⊢ [ ρ ] X ∈̂[ resGr Γ V [ σ ]ʳ ] Γ₀ ] (⌊ R ⌋ʳ ≡ V [ ι ⨟ˢ σ ]ᴿᵛ)
soundR {σ = σ} ι Γ (var i) refl s {ρ} {X} e =
  res-var z , cong var (trans (var-pos-cast ety egr x) (var-pos-lookup (Γ [ σ ]ᶜᵗˣ) i))
  where
    ety = trans (lookup-ty-subst Γ σ i) e
    egr = lookup-gr-subst Γ σ i
    x   = lookup-var (Γ [ σ ]ᶜᵗˣ) i
    z   = mem-cast ety egr x
soundR {σ = σ} {Q = Q} ι Γ (V ⦂ᵛ B) ceq (s , sa) {ρ} {X} e
  with <:̂ᵛ-boxʳ (subst (Q ⊩ resTy ι Γ V [ σ ]ᵛ <:̂ᵛ_) e sa)
... | ρ₁ , X₁ , e₁ , q , p with soundR ι Γ V ceq s e₁
...   | R , er =
  res-ann ρ X R q p , cong₂ _⦂ᵛ_ er (trans (sym e) ([⨟]ᵛ B ι σ))
soundR ι Γ (usedef k)    ceq () e
soundR ι Γ (const B c)   ceq () e
soundR ι Γ ⋆             ceq () e
soundR ι Γ true          ceq () e
soundR ι Γ false         ceq () e
soundR ι Γ zero          ceq () e
soundR ι Γ (succ V)      ceq () e
soundR ι Γ ⦉ V , W ⦊      ceq () e
soundR ι Γ (inl V)       ceq () e
soundR ι Γ (inr V)       ceq () e
soundR ι Γ nil           ceq () e
soundR ι Γ (cons V W)    ceq () e
soundR ι Γ (cmp ⋈ V W)   ceq () e
soundR ι Γ (fun M)       ceq () e
soundR ι Γ (handler N H) ceq () e

mutual

  soundVˢ : ∀ {Θ₀ Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
          → (ι : Subst Θ₀ Θ) → (Γ : OCtx Θ n) → (V : RawV Θ₀ n) → (A : OVType Θ)
          → σ ⊨[ Q ] genVˢ ι Γ V A
          --------------------------------------------------------------------
          → Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢ᵛ⦂ A [ σ ]ᵛ) ] (⌊ D ⌋ᵛ ≡ V [ ι ⨟ˢ σ ]ᴿᵛ)

  -- variables: the witness is `lookup-var`, at position `i`; the `Et∨≾ᵘ`
  -- conjunct is `_⊩_Et∨≾ᵘ_`, the subtyping atom the `subV` to the expected type

  soundVˢ {σ = σ} {Q = Q} ι Γ (var i) A (st , ok) =
    subV D₀ st' , cong var (var-pos-lookup (Γ [ σ ]ᶜᵗˣ) i)
    where
      x = lookup-var (Γ [ σ ]ᶜᵗˣ) i

      ok₁ = subst₂ (Q ⊩_Et∨≾ᵘ_)
                   (sym (lookup-ty-subst Γ σ i))
                   (sym (lookup-gr-subst Γ σ i))
                   ok

      D₀ = var x ok₁

      st' = subst (λ z → Q ⊩ z <:̂ᵛ A [ σ ]ᵛ) (sym (lookup-ty-subst Γ σ i)) st

  -- uses of definitions

  soundVˢ {σ = σ} ι Γ (usedef k) A s = soundUseDef σ Γ k A s

  -- base-typed constants, unit, booleans: the type equation's first half is
  -- the `subV` into the expected type

  soundVˢ ι Γ (const B c) A (st , _) = subV (const B c) st , refl
  soundVˢ ι Γ ⋆           A (st , _) = subV ⋆ st           , refl
  soundVˢ ι Γ true        A (st , _) = subV true st        , refl
  soundVˢ ι Γ false       A (st , _) = subV false st       , refl

  -- natural numbers

  soundVˢ ι Γ zero        A (st , _) = subV zero st        , refl
  soundVˢ ι Γ (succ V)    A ((st , _) , s) =
    subV (succ (proj₁ ih)) st , cong succ (proj₂ ih)
    where
      ih = soundVˢ ι Γ V nat s

  -- pairing

  soundVˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ ⦉ V₁ , V₂ ⦊ A (B₁ , B₂ , (st , _) , s₁ , s₂) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})

      pΓ = co²ᵗ-ctx σ B₁ B₂ Γ
      pA = co²ᵗ-v   σ B₁ B₂ A
      pι = co²ᵗ-ˢ   ι σ B₁ B₂

      ih₁ = soundVˢ ι↑ Γ↑ V₁ α₁ s₁
      ih₂ = soundVˢ ι↑ Γ↑ V₂ α₂ s₂

      D₁ = ctx-substᵛ pΓ (proj₁ ih₁)
      D₂ = ctx-substᵛ pΓ (proj₁ ih₂)

      D = subV ⦉ D₁ , D₂ ⦊ (subst (λ z → Q ⊩ _ <:̂ᵛ z) pA st)

      q = cong₂ ⦉_,_⦊
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᵛ pι V₁)))
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₂)) (trans (proj₂ ih₂) ([≐]ᴿᵛ pι V₂)))

  -- injections into a sum

  soundVˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (inl V) A (B₁ , B₂ , (st , _) , s₁) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))

      pΓ = co²ᵗ-ctx σ B₁ B₂ Γ
      pA = co²ᵗ-v   σ B₁ B₂ A
      pι = co²ᵗ-ˢ   ι σ B₁ B₂

      ih₁ = soundVˢ ι↑ Γ↑ V α₁ s₁

      D₁ = ctx-substᵛ pΓ (proj₁ ih₁)

      D = subV (inl {B = B₂} D₁) (subst (λ z → Q ⊩ B₁ |+| B₂ <:̂ᵛ z) pA st)

      q = cong inl (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᵛ pι V)))

  soundVˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (inr V) A (B₁ , B₂ , (st , _) , s₂) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)
      α₂ = tvar (newᵗ {Θ +ty})

      pΓ = co²ᵗ-ctx σ B₁ B₂ Γ
      pA = co²ᵗ-v   σ B₁ B₂ A
      pι = co²ᵗ-ˢ   ι σ B₁ B₂

      ih₂ = soundVˢ ι↑ Γ↑ V α₂ s₂

      D₂ = ctx-substᵛ pΓ (proj₁ ih₂)

      D = subV (inr {A = B₁} D₂) (subst (λ z → Q ⊩ B₁ |+| B₂ <:̂ᵛ z) pA st)

      q = cong inr (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₂)) (trans (proj₂ ih₂) ([≐]ᴿᵛ pι V)))

  -- lists

  soundVˢ {σ = σ} {Q = Q} ι Γ nil A (B , (st , _)) =
    subV (nil {A = B}) (subst (λ z → Q ⊩ list B <:̂ᵛ z) (wk-,ᵗ-v σ B A) st) , refl

  soundVˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (cons V W) A (B , (st , _) , s₁ , s₂) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx Γ
      α  = tvar (newᵗ {Θ})

      pΓ = wk-,ᵗ-ctx σ B Γ
      pA = wk-,ᵗ-v   σ B A
      pι = wk-,ᵗ-ˢ   ι σ B

      ih₁ = soundVˢ ι↑ Γ↑ V α s₁
      ih₂ = soundVˢ ι↑ Γ↑ W (list α) s₂

      D₁ = ctx-substᵛ pΓ (proj₁ ih₁)
      D₂ = ctx-substᵛ pΓ (proj₁ ih₂)

      D = subV (cons D₁ D₂) (subst (λ z → Q ⊩ list B <:̂ᵛ z) pA st)

      q = cong₂ cons
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᵛ pι V)))
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₂)) (trans (proj₂ ih₂) ([≐]ᴿᵛ pι W)))

  -- comparison: the witness is the operands' type, eternal by `Etᶜ`; the type
  -- equation's first half is the `subV` into the expected type

  soundVˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (cmp ⋈ V W) A (B , (st , _) , s₁ , s₂ , et) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx Γ
      α  = tvar (newᵗ {Θ})

      pΓ = wk-,ᵗ-ctx σ B Γ
      pA = wk-,ᵗ-v   σ B A
      pι = wk-,ᵗ-ˢ   ι σ B

      ih₁ = soundVˢ ι↑ Γ↑ V α s₁
      ih₂ = soundVˢ ι↑ Γ↑ W α s₂

      D₁ = ctx-substᵛ pΓ (proj₁ ih₁)
      D₂ = ctx-substᵛ pΓ (proj₁ ih₂)

      D = subV (cmp ⋈ D₁ D₂ et) (subst (λ z → Q ⊩ bool <:̂ᵛ z) pA st)

      q = cong₂ (cmp ⋈)
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᵛ pι V)))
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₂)) (trans (proj₂ ih₂) ([≐]ᴿᵛ pι W)))

  -- lambda abstraction

  soundVˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (fun M) A (B₁ , B₂ , ε , st , s) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))
      α₁ = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      α₂ = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})

      pΓ = co²ᵗᵉ-ctx σ B₁ B₂ ε Γ
      pA = co²ᵗᵉ-v   σ B₁ B₂ ε A
      pι = co²ᵗᵉ-ˢ   ι σ B₁ B₂ ε

      ih = soundCˢ ι↑ (Γ↑ ∷ α₁) M α₂ e s

      D₀ = ctx-substᶜ (cong (_∷ _) pΓ) (proj₁ ih)

      D = subV (fun D₀) (subst (λ z → Q ⊩ _ <:̂ᵛ z) pA st)

      q = cong fun (trans (⌊ctxᶜ⌋ (cong (_∷ _) pΓ) (proj₁ ih))
                          (trans (proj₂ ih) ([≐]ᴿᶜ pι M)))

  -- handlers: the clause family one `∀ᵉ` deeper; its erasure needs `fun-ext`

  soundVˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (handler N H) A
          (B₁ , B₂ , ε₁ , ε₂ , st , s₂ , cls) =
    D , q
    where
      ι↑  = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ
      σ'  = σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε₁ ,ᵉ ε₂
      Γ↑  = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ)))
      α   = wkᵉ-v (wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ}))))
      γ   = wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ +ty})))
      e₁  = wkᵉ-e (evar (newᵉ {Θ +ty +ty}))
      e₂  = evar (newᵉ {Θ +ty +ty +e})
      Γ⇑  = wkᵉ-ctx (wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))))
      γ⇑  = wkᵉ-v (wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ +ty}))))
      e'' = evar (newᵉ {Θ +ty +ty +e +e})

      pΓ  = co²ᵗ²ᵉ-ctx  σ B₁ B₂ ε₁ ε₂ Γ
      pA  = co²ᵗ²ᵉ-v    σ B₁ B₂ ε₁ ε₂ A
      pΓ⇑ = co²ᵗ²ᵉ-ctx↑ σ B₁ B₂ ε₁ ε₂ Γ
      pγ⇑ = wk-↑ᵉ-v σ' γ
      pι  = co²ᵗ²ᵉ-ˢ    ι σ B₁ B₂ ε₁ ε₂
      pι⇑ = co²ᵗ²ᵉ-ˢ↑   ι σ B₁ B₂ ε₁ ε₂

      ih₂ = soundCˢ ι↑ (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) N γ e₂ s₂

      c₂ = cong (λ Γ₀ → Γ₀ ⟨ ∣ ε₁ ∣̂ᵉ ⟩ ∷ B₁) pΓ

      D₂ = ctx-substᶜ c₂ (proj₁ ih₂)

      ihH : (op : Op) → _
      ihH op =
        soundCˢ (ι↑ ↑ᵉ)
                (Γ⇑ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                    ∷ [ rconst ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ γ⇑ ! e''))
                (H op) γ⇑ (econst (op-grade op) ·̂ₑ e'') (cls op)

      cH : (op : Op) → _
      cH op =
        cong₂ _∷_
              (cong₂ _∷_ (cong (_⟨ rconst ⊤ᵣ ⟩) pΓ⇑) (⌜⌝ᵍ-subst (σ' ↑ᵉ) (param op)))
              (cong₂ (λ A₀ B₀ → [ rconst ∣ op-grade op ∣ᵉ ] (A₀ ⇒ B₀ ! _))
                     (⌜⌝ᵍ-subst (σ' ↑ᵉ) (arity op))
                     pγ⇑)

      DH : (op : Op) → _
      DH op = c-subst (cong (_! _) pγ⇑) (ctx-substᶜ (cH op) (proj₁ (ihH op)))

      D = subV (handler D₂ DH) (subst (λ z → Q ⊩ _ <:̂ᵛ z) pA st)

      q = cong₂ handler
                (trans (⌊ctxᶜ⌋ c₂ (proj₁ ih₂)) (trans (proj₂ ih₂) ([≐]ᴿᶜ pι N)))
                (fun-ext (λ op →
                   trans (⌊c⌋ (cong (_! _) pγ⇑) (ctx-substᶜ (cH op) (proj₁ (ihH op))))
                         (trans (⌊ctxᶜ⌋ (cH op) (proj₁ (ihH op)))
                                (trans (proj₂ (ihH op)) ([≐]ᴿᶜ pι⇑ (H op))))))

  -- type annotation: the recording rule at the instantiated annotation, then
  -- the atom as a `subV`

  soundVˢ {σ = σ} ι Γ (V ⦂ᵛ B) A (s , st) =
    subV (annᵛ (B [ ι ]ᵛ [ σ ]ᵛ) (proj₁ ih)) st ,
    cong₂ _⦂ᵛ_ (proj₂ ih) ([⨟]ᵛ B ι σ)
    where
      ih = soundVˢ ι Γ V (B [ ι ]ᵛ) s


  soundCˢ : ∀ {Θ₀ Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
          → (ι : Subst Θ₀ Θ) → (Γ : OCtx Θ n) → (M : RawC Θ₀ n)
          → (A : OVType Θ) → (t : EExp Θ)
          → σ ⊨[ Q ] genCˢ ι Γ M (A ! t)
          ---------------------------------------------------------------------
          → Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢ᶜ⦂ A [ σ ]ᵛ ! t [ σ ]ᵉ) ]
              (⌊ D ⌋ᶜ ≡ M [ ι ⨟ˢ σ ]ᴿᶜ)

  -- returning a value

  soundCˢ ι Γ (return V) A t (s , le) =
    coerce le (return (proj₁ ih)) , cong return (proj₂ ih)
    where
      ih = soundVˢ ι Γ V A s

  -- sequential composition

  soundCˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (M₁ ⨟ M₂) A t (B , ε₁ , ε₂ , s₁ , s₂ , le) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ
      Γ↑ = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx Γ))
      A↑ = wkᵉ-v (wkᵉ-v (wkᵗ-v A))
      α  = wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ})))
      e₁ = wkᵉ-e (evar (newᵉ {Θ +ty}))
      e₂ = evar (newᵉ {Θ +ty +e})

      pΓ = coᵗ²ᵉ-ctx σ B ε₁ ε₂ Γ
      pA = coᵗ²ᵉ-v   σ B ε₁ ε₂ A
      pt = coᵗ²ᵉ-e   σ B ε₁ ε₂ t
      pι = coᵗ²ᵉ-ˢ   ι σ B ε₁ ε₂

      ih₁ = soundCˢ ι↑ Γ↑ M₁ α e₁ s₁
      ih₂ = soundCˢ ι↑ (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) M₂ A↑ e₂ s₂

      c₂ = cong (λ Γ₀ → Γ₀ ⟨ _ ⟩ ∷ _) pΓ

      D₁ = ctx-substᶜ pΓ (proj₁ ih₁)
      D₂ = c-subst (cong (_! _) pA) (ctx-substᶜ c₂ (proj₁ ih₂))

      D = coerce (subst (λ x → Q ⊩ _ ≾̂ₑ x) pt le) (D₁ ⨟ D₂)

      q = cong₂ _⨟_
                (trans (⌊ctxᶜ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᶜ pι M₁)))
                (trans (⌊c⌋ (cong (_! _) pA) (ctx-substᶜ c₂ (proj₁ ih₂)))
                       (trans (⌊ctxᶜ⌋ c₂ (proj₁ ih₂))
                              (trans (proj₂ ih₂) ([≐]ᴿᶜ pι M₂))))

  -- function application

  soundCˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (V₁ · V₂) A t (B₁ , B₂ , ε , s₁ , s₂ , st , le) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))
      α  = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      β  = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})

      pΓ = co²ᵗᵉ-ctx σ B₁ B₂ ε Γ
      pA = co²ᵗᵉ-v   σ B₁ B₂ ε A
      pt = co²ᵗᵉ-e   σ B₁ B₂ ε t
      pι = co²ᵗᵉ-ˢ   ι σ B₁ B₂ ε

      ih₁ = soundVˢ ι↑ Γ↑ V₁ (α ⇒ (β ! e)) s₁
      ih₂ = soundVˢ ι↑ Γ↑ V₂ α s₂

      D₁ = ctx-substᵛ pΓ (proj₁ ih₁)
      D₂ = ctx-substᵛ pΓ (proj₁ ih₂)

      D = subC (D₁ · D₂)
               (subst (λ z → Q ⊩ _ <:̂ᵛ z) pA st
                  !ₛ subst (λ z → Q ⊩ _ ≾̂ₑ z) pt le)

      q = cong₂ _·_
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᵛ pι V₁)))
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₂)) (trans (proj₂ ih₂) ([≐]ᴿᵛ pι V₂)))

  -- pattern-matching

  soundCˢ {Θ = Θ} {σ = σ} ι Γ (match V `with M) A t (B₁ , B₂ , s₁ , s₂) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)
      A↑ = wkᵗ-v (wkᵗ-v A)
      t↑ = wkᵗ-e (wkᵗ-e t)
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})

      pΓ = co²ᵗ-ctx σ B₁ B₂ Γ
      pA = co²ᵗ-v   σ B₁ B₂ A
      pt = co²ᵗ-e   σ B₁ B₂ t
      pι = co²ᵗ-ˢ   ι σ B₁ B₂

      ih₁ = soundVˢ ι↑ Γ↑ V (α₁ |×| α₂) s₁
      ih₂ = soundCˢ ι↑ (Γ↑ ∷ α₁ ∷ α₂) M A↑ t↑ s₂

      c₂ = cong (λ Γ₀ → Γ₀ ∷ _ ∷ _) pΓ

      D₁ = ctx-substᵛ pΓ (proj₁ ih₁)
      D₂ = c-subst (cong₂ _!_ pA pt) (ctx-substᶜ c₂ (proj₁ ih₂))

      D = match D₁ `with D₂

      q = cong₂ match_`with_
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᵛ pι V)))
                (trans (⌊c⌋ (cong₂ _!_ pA pt) (ctx-substᶜ c₂ (proj₁ ih₂)))
                       (trans (⌊ctxᶜ⌋ c₂ (proj₁ ih₂))
                              (trans (proj₂ ih₂) ([≐]ᴿᶜ pι M))))

  -- empty type elimination

  soundCˢ ι Γ (absurd V) A t s =
    absurd (proj₁ ih) , cong absurd (proj₂ ih)
    where
      ih = soundVˢ ι Γ V empty s

  -- boolean elimination

  soundCˢ ι Γ (if V `then M₁ `else M₂) A t (s₀ , s₁ , s₂) =
    if (proj₁ ih₀) `then (proj₁ ih₁) `else (proj₁ ih₂) ,
    cong₃ if_`then_`else_ (proj₂ ih₀) (proj₂ ih₁) (proj₂ ih₂)
    where
      ih₀ = soundVˢ ι Γ V bool s₀
      ih₁ = soundCˢ ι Γ M₁ A t s₁
      ih₂ = soundCˢ ι Γ M₂ A t s₂

  -- natural-number elimination

  soundCˢ ι Γ (matchℕ V `zero M₁ `succ M₂) A t (s₀ , s₁ , s₂) =
    matchℕ (proj₁ ih₀) `zero (proj₁ ih₁) `succ (proj₁ ih₂) ,
    cong₃ matchℕ_`zero_`succ_ (proj₂ ih₀) (proj₂ ih₁) (proj₂ ih₂)
    where
      ih₀ = soundVˢ ι Γ V nat s₀
      ih₁ = soundCˢ ι Γ M₁ A t s₁
      ih₂ = soundCˢ ι (Γ ∷ nat) M₂ A t s₂

  -- sum elimination

  soundCˢ {Θ = Θ} {σ = σ} ι Γ (match+ V `inl M₁ `inr M₂) A t (B₁ , B₂ , s₀ , s₁ , s₂) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)
      A↑ = wkᵗ-v (wkᵗ-v A)
      t↑ = wkᵗ-e (wkᵗ-e t)
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})

      pΓ = co²ᵗ-ctx σ B₁ B₂ Γ
      pA = co²ᵗ-v   σ B₁ B₂ A
      pt = co²ᵗ-e   σ B₁ B₂ t
      pι = co²ᵗ-ˢ   ι σ B₁ B₂
      pC = cong₂ _!_ pA pt

      ih₀ = soundVˢ ι↑ Γ↑ V (α₁ |+| α₂) s₀
      ih₁ = soundCˢ ι↑ (Γ↑ ∷ α₁) M₁ A↑ t↑ s₁
      ih₂ = soundCˢ ι↑ (Γ↑ ∷ α₂) M₂ A↑ t↑ s₂

      c₁ = cong (_∷ B₁) pΓ
      c₂ = cong (_∷ B₂) pΓ

      D₀ = ctx-substᵛ pΓ (proj₁ ih₀)
      D₁ = c-subst pC (ctx-substᶜ c₁ (proj₁ ih₁))
      D₂ = c-subst pC (ctx-substᶜ c₂ (proj₁ ih₂))

      D = match+ D₀ `inl D₁ `inr D₂

      q = cong₃ match+_`inl_`inr_
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₀)) (trans (proj₂ ih₀) ([≐]ᴿᵛ pι V)))
                (trans (⌊c⌋ pC (ctx-substᶜ c₁ (proj₁ ih₁)))
                       (trans (⌊ctxᶜ⌋ c₁ (proj₁ ih₁))
                              (trans (proj₂ ih₁) ([≐]ᴿᶜ pι M₁))))
                (trans (⌊c⌋ pC (ctx-substᶜ c₂ (proj₁ ih₂)))
                       (trans (⌊ctxᶜ⌋ c₂ (proj₁ ih₂))
                              (trans (proj₂ ih₂) ([≐]ᴿᶜ pι M₂))))

  -- primitive recursion on natural numbers

  soundCˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (recℕ V M₁ M₂) A t
          (B , ε , s₀ , s₁ , s₂ , it , st , le) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx Γ)
      β  = wkᵉ-v (tvar (newᵗ {Θ}))
      e  = evar (newᵉ {Θ +ty})

      pΓ = coᵗᵉ-ctx σ B ε Γ
      pA = coᵗᵉ-v   σ B ε A
      pt = coᵗᵉ-e   σ B ε t
      pι = coᵗᵉ-ˢ   ι σ B ε

      ih₀ = soundVˢ ι↑ Γ↑ V nat s₀
      ih₁ = soundCˢ ι↑ Γ↑ M₁ β e s₁
      ih₂ = soundCˢ ι↑ ((Γ↑ ⟨ rconst ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ e ∣̂ᵉ ⟩ ∷ β) M₂ β e s₂

      c₂ = cong (λ Γ₀ → (Γ₀ ⟨ rconst ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B) pΓ

      D₀ = ctx-substᵛ pΓ (proj₁ ih₀)
      D₁ = ctx-substᶜ pΓ (proj₁ ih₁)
      D₂ = ctx-substᶜ c₂ (proj₁ ih₂)

      D = subC (recℕ D₀ D₁ D₂ it)
               (subst (λ z → Q ⊩ _ <:̂ᵛ z) pA st
                  !ₛ subst (λ z → Q ⊩ _ ≾̂ₑ z) pt le)

      q = cong₃ recℕ
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₀)) (trans (proj₂ ih₀) ([≐]ᴿᵛ pι V)))
                (trans (⌊ctxᶜ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᶜ pι M₁)))
                (trans (⌊ctxᶜ⌋ c₂ (proj₁ ih₂)) (trans (proj₂ ih₂) ([≐]ᴿᶜ pι M₂)))

  -- list elimination

  soundCˢ {Θ = Θ} {σ = σ} ι Γ (matchL V `nil M₁ `cons M₂) A t (B , s₀ , s₁ , s₂) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx Γ
      A↑ = wkᵗ-v A
      t↑ = wkᵗ-e t
      α  = tvar (newᵗ {Θ})

      pΓ = wk-,ᵗ-ctx σ B Γ
      pA = wk-,ᵗ-v   σ B A
      pt = wk-,ᵗ-e   σ B t
      pι = wk-,ᵗ-ˢ   ι σ B
      pC = cong₂ _!_ pA pt

      ih₀ = soundVˢ ι↑ Γ↑ V (list α) s₀
      ih₁ = soundCˢ ι↑ Γ↑ M₁ A↑ t↑ s₁
      ih₂ = soundCˢ ι↑ (Γ↑ ∷ α ∷ list α) M₂ A↑ t↑ s₂

      c₂ = cong (λ G → G ∷ B ∷ list B) pΓ

      D₀ = ctx-substᵛ pΓ (proj₁ ih₀)
      D₁ = c-subst pC (ctx-substᶜ pΓ (proj₁ ih₁))
      D₂ = c-subst pC (ctx-substᶜ c₂ (proj₁ ih₂))

      D = matchL D₀ `nil D₁ `cons D₂

      q = cong₃ matchL_`nil_`cons_
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₀)) (trans (proj₂ ih₀) ([≐]ᴿᵛ pι V)))
                (trans (⌊c⌋ pC (ctx-substᶜ pΓ (proj₁ ih₁)))
                       (trans (⌊ctxᶜ⌋ pΓ (proj₁ ih₁))
                              (trans (proj₂ ih₁) ([≐]ᴿᶜ pι M₁))))
                (trans (⌊c⌋ pC (ctx-substᶜ c₂ (proj₁ ih₂)))
                       (trans (⌊ctxᶜ⌋ c₂ (proj₁ ih₂))
                              (trans (proj₂ ih₂) ([≐]ᴿᶜ pι M₂))))

  -- primitive recursion on lists

  soundCˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (recL V M₁ M₂) A t
          (B₁ , B₂ , ε , s₀ , s₁ , s₂ , it , st , le) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))
      α  = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      β  = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})

      pΓ = co²ᵗᵉ-ctx σ B₁ B₂ ε Γ
      pA = co²ᵗᵉ-v   σ B₁ B₂ ε A
      pt = co²ᵗᵉ-e   σ B₁ B₂ ε t
      pι = co²ᵗᵉ-ˢ   ι σ B₁ B₂ ε

      ih₀ = soundVˢ ι↑ Γ↑ V (list α) s₀
      ih₁ = soundCˢ ι↑ Γ↑ M₁ β e s₁
      ih₂ = soundCˢ ι↑ ((Γ↑ ⟨ rconst ⊤ᵣ ⟩ ∷ α ∷ list α) ⟨ ∣ e ∣̂ᵉ ⟩ ∷ β) M₂ β e s₂

      c₂ = cong (λ Γ₀ → (Γ₀ ⟨ rconst ⊤ᵣ ⟩ ∷ B₁ ∷ list B₁) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B₂) pΓ

      D₀ = ctx-substᵛ pΓ (proj₁ ih₀)
      D₁ = ctx-substᶜ pΓ (proj₁ ih₁)
      D₂ = ctx-substᶜ c₂ (proj₁ ih₂)

      D = subC (recL D₀ D₁ D₂ it)
               (subst (λ z → Q ⊩ _ <:̂ᵛ z) pA st
                  !ₛ subst (λ z → Q ⊩ _ ≾̂ₑ z) pt le)

      q = cong₃ recL
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₀)) (trans (proj₂ ih₀) ([≐]ᴿᵛ pι V)))
                (trans (⌊ctxᶜ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᶜ pι M₁)))
                (trans (⌊ctxᶜ⌋ c₂ (proj₁ ih₂)) (trans (proj₂ ih₂) ([≐]ᴿᶜ pι M₂)))

  -- performing algebraic operations

  soundCˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (perform op V M) A t (ε , s₁ , s₂ , le) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵉ
      σ' = σ ,ᵉ ε
      Γ↑ = wkᵉ-ctx Γ
      A↑ = wkᵉ-v A
      e  = evar (newᵉ {Θ})

      pΓ = wk-,ᵉ-ctx σ ε Γ
      pA = wk-,ᵉ-v   σ ε A
      pt = wk-,ᵉ-e   σ ε t
      pι = wk-,ᵉ-ˢ   ι σ ε
      pp = ⌜⌝ᵍ-subst σ' (param op)
      pa = ⌜⌝ᵍ-subst σ' (arity op)

      ih₁ = soundVˢ ι↑ Γ↑ V ⌜ param op ⌝ᵍ s₁
      ih₂ = soundCˢ ι↑ (Γ↑ ⟨ rconst ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ) M A↑ e s₂

      c₂ = cong₂ (λ Γ₀ A₀ → Γ₀ ⟨ rconst ∣ op-grade op ∣ᵉ ⟩ ∷ A₀) pΓ pa

      D₁ = ty-subst pp (ctx-substᵛ pΓ (proj₁ ih₁))
      D₂ = c-subst (cong (_! _) pA) (ctx-substᶜ c₂ (proj₁ ih₂))

      D = coerce (subst (λ x → Q ⊩ _ ≾̂ₑ x) pt le) (perform op D₁ D₂)

      q = cong₂ (perform op)
                (trans (⌊ty⌋ pp (ctx-substᵛ pΓ (proj₁ ih₁)))
                       (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₁))
                              (trans (proj₂ ih₁) ([≐]ᴿᵛ pι V))))
                (trans (⌊c⌋ (cong (_! _) pA) (ctx-substᶜ c₂ (proj₁ ih₂)))
                       (trans (⌊ctxᶜ⌋ c₂ (proj₁ ih₂))
                              (trans (proj₂ ih₂) ([≐]ᴿᶜ pι M))))

  -- explicit delaying of a computation

  soundCˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (delay τ M) A t (ε , s , le) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵉ
      Γ↑ = wkᵉ-ctx Γ
      A↑ = wkᵉ-v A
      e  = evar (newᵉ {Θ})

      pΓ = wk-,ᵉ-ctx σ ε Γ
      pA = wk-,ᵉ-v   σ ε A
      pt = wk-,ᵉ-e   σ ε t
      pι = wk-,ᵉ-ˢ   ι σ ε

      ih = soundCˢ ι↑ (Γ↑ ⟨ rconst (ιᵣ τ) ⟩) M A↑ e s

      c₀ = cong (_⟨ rconst (ιᵣ τ) ⟩) pΓ

      D₀ = c-subst (cong (_! _) pA) (ctx-substᶜ c₀ (proj₁ ih))

      D = coerce (subst (λ x → Q ⊩ _ ≾̂ₑ x) pt le) (delay τ D₀)

      q = cong (delay τ)
               (trans (⌊c⌋ (cong (_! _) pA) (ctx-substᶜ c₀ (proj₁ ih)))
                      (trans (⌊ctxᶜ⌋ c₀ (proj₁ ih))
                             (trans (proj₂ ih) ([≐]ᴿᶜ pι M))))

  -- effect handling

  soundCˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (handle M `with V) A t
          (B₁ , B₂ , ε₁ , ε₂ , s₁ , sV , st , le) =
    D , q
    where
      ι↑  = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ
      Γ↑  = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ)))
      α   = wkᵉ-v (wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ}))))
      γ   = wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ +ty})))
      e₁  = wkᵉ-e (evar (newᵉ {Θ +ty +ty}))
      e₂  = evar (newᵉ {Θ +ty +ty +e})

      pΓ  = co²ᵗ²ᵉ-ctx  σ B₁ B₂ ε₁ ε₂ Γ
      pA  = co²ᵗ²ᵉ-v    σ B₁ B₂ ε₁ ε₂ A
      pt  = co²ᵗ²ᵉ-e    σ B₁ B₂ ε₁ ε₂ t
      pι  = co²ᵗ²ᵉ-ˢ    ι σ B₁ B₂ ε₁ ε₂

      ih₁ = soundCˢ ι↑ Γ↑ M α e₁ s₁
      ihV = soundVˢ ι↑ Γ↑ V ((α ! e₁) ⇛ (γ ! e₂)) sV

      D₁ = ctx-substᶜ pΓ (proj₁ ih₁)
      DV = ctx-substᵛ pΓ (proj₁ ihV)

      D = subC (handle D₁ `with DV)
               (subst (λ z → Q ⊩ _ <:̂ᵛ z) pA st
                  !ₛ subst (λ z → Q ⊩ _ ≾̂ₑ z) pt le)

      q = cong₂ handle_`with_
                (trans (⌊ctxᶜ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᶜ pι M)))
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ihV)) (trans (proj₂ ihV) ([≐]ᴿᵛ pι V)))

  -- unboxing a resource value: the `∃ᵗ` witness is equivalent to the payload,
  -- the `∃ʳ` one between the variable's grade and the grade reached

  soundCˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (unbox V N) A t (B , ρ , sR , (sb , sb') , le , s')
    with <:̂ᵛ-boxʳ sb
  ... | ρ₁ , X₁ , e₁ , q₁ , p₁
    with soundR (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢʳ) (wkʳ-ctx (wkᵗ-ctx Γ)) V (coᵗʳ-ctx σ B ρ Γ) sR e₁
  ...   | R , er = D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢʳ
      σ' = σ ,ᵗ B ,ʳ ρ
      Γ↑ = wkʳ-ctx (wkᵗ-ctx Γ)
      A↑ = wkʳ-v (wkᵗ-v A)
      t↑ = wkʳ-e (wkᵗ-e t)
      β  = wkʳ-v (tvar (newᵗ {Θ}))

      pΓ = coᵗʳ-ctx σ B ρ Γ
      pA = coᵗʳ-v   σ B ρ A
      pt = coᵗʳ-e   σ B ρ t
      pι = coᵗʳ-ˢ   ι σ B ρ

      -- the `∃ᵗ`-bound variable is the binder `B`

      pβ = wk-,ʳ-v (σ ,ᵗ B) ρ (tvar (newᵗ {Θ}))

      ih = soundCˢ ι↑ (Γ↑ ∷ β) N A↑ t↑ s'

      c₀ = cong₂ _∷_ pΓ pβ

      D₀ = c-subst (cong₂ _!_ pA pt) (ctx-substᶜ c₀ (proj₁ ih))

      -- the payload and the binder are equivalent

      eqv = subst (Q ⊩ X₁ <:̂ᵛ_) pβ p₁
          , subst (Q ⊩_<:̂ᵛ X₁) pβ (<:̂ᵛ-box-type (subst (Q ⊩ [ ρ ] _ <:̂ᵛ_) e₁ sb'))

      D₁ = conv-last equivalence eqv D₀

      D = unbox R (transᵣ le q₁) (proj₁ D₁)

      q = cong₂ unbox
                (trans er ([≐]ᴿᵛ pι V))
                (trans (proj₂ D₁)
                (trans (⌊c⌋ (cong₂ _!_ pA pt) (ctx-substᶜ c₀ (proj₁ ih)))
                       (trans (⌊ctxᶜ⌋ c₀ (proj₁ ih))
                              (trans (proj₂ ih) ([≐]ᴿᶜ pι N)))))

  -- boxing up a value: the grade is the instantiated annotation, the payload's
  -- type the only witness

  soundCˢ {Θ = Θ} {σ = σ} ι Γ (box ρ V N) A t (B , s₁ , s₂) =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      σ' = σ ,ᵗ B
      Γ↑ = wkᵗ-ctx Γ
      A↑ = wkᵗ-v A
      t↑ = wkᵗ-e t
      α  = tvar (newᵗ {Θ})
      r  = ρ [ ι↑ ]ʳ
      ρ' = ρ [ ι ⨟ˢ σ ]ʳ

      pΓ = wk-,ᵗ-ctx σ B Γ
      pA = wk-,ᵗ-v   σ B A
      pt = wk-,ᵗ-e   σ B t
      pι = wk-,ᵗ-ˢ   ι σ B

      pr : r [ σ' ]ʳ ≡ ρ'
      pr = trans ([⨟]ʳ ρ ι↑ σ') ([≐]ʳ pι ρ)

      ih₁ = soundVˢ ι↑ (Γ↑ ⟨ r ⟩) V α s₁
      ih₂ = soundCˢ ι↑ (Γ↑ ∷ [ r ] α) N A↑ t↑ s₂

      c₁ = cong₂ _⟨_⟩ pΓ pr
      c₂ = cong₂ (λ Γ₀ ρ₀ → Γ₀ ∷ [ ρ₀ ] B) pΓ pr

      D₁ = ctx-substᵛ c₁ (proj₁ ih₁)
      D₂ = c-subst (cong₂ _!_ pA pt) (ctx-substᶜ c₂ (proj₁ ih₂))

      D = box ρ' D₁ D₂

      q = cong₂ (box ρ')
                (trans (⌊ctxᵛ⌋ c₁ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᵛ pι V)))
                (trans (⌊c⌋ (cong₂ _!_ pA pt) (ctx-substᶜ c₂ (proj₁ ih₂)))
                       (trans (⌊ctxᶜ⌋ c₂ (proj₁ ih₂))
                              (trans (proj₂ ih₂) ([≐]ᴿᶜ pι N))))

  -- type annotation: as for values, the two atoms making up the `subC`

  soundCˢ {σ = σ} ι Γ (M ⦂ᶜ (B ! u)) A t (s , st , le) =
    subC (annᶜ (B [ ι ]ᵛ [ σ ]ᵛ ! u [ ι ]ᵉ [ σ ]ᵉ) (proj₁ ih)) (st !ₛ le) ,
    cong₂ _⦂ᶜ_ (proj₂ ih) ([⨟]ᶜ (B ! u) ι σ)
    where
      ih = soundCˢ ι Γ M (B [ ι ]ᵛ) (u [ ι ]ᵉ) s

-- Generation for a raw term over the context's scope, the program's annotations
-- instantiated by the solution

soundV : ∀ {Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
       → (Γ : OCtx Θ n) → (V : RawV Θ n) → (A : OVType Θ)
       → σ ⊨[ Q ] genV Γ V A
       --------------------------------------------------------------
       → Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢ᵛ⦂ A [ σ ]ᵛ) ] (⌊ D ⌋ᵛ ≡ V [ σ ]ᴿᵛ)

soundV {σ = σ} Γ V A s =
  proj₁ ih , trans (proj₂ ih) ([≐]ᴿᵛ (⨟-idˡ σ) V)
  where
    ih = soundVˢ idˢ Γ V A s

soundC : ∀ {Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
       → (Γ : OCtx Θ n) → (M : RawC Θ n) → (A : OVType Θ) → (t : EExp Θ)
       → σ ⊨[ Q ] genC Γ M (A ! t)
       -----------------------------------------------------------------------
       → Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢ᶜ⦂ A [ σ ]ᵛ ! t [ σ ]ᵉ) ] (⌊ D ⌋ᶜ ≡ M [ σ ]ᴿᶜ)

soundC {σ = σ} Γ M A t s =
  proj₁ ih , trans (proj₂ ih) ([≐]ᴿᶜ (⨟-idˡ σ) M)
  where
    ih = soundCˢ idˢ Γ M A t s

-- Sanity checks: five closed examples, solved by the identity substitution from
-- no hypotheses, elaborated and erased back

private

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  -- returning a value: the `≾̂ₑᶜ` conjunct becomes a `coerce`, the type
  -- equation's first half a `subV`

  ex-return : ∅ᴴ ∣ ∅ᶜ ∷ unit ⊢ᶜ⦂ unit ! 𝟏̂ₑ
  ex-return = proj₁ (soundC {σ = idˢ} {Q = ∅ᴴ} (∅ᶜ ∷ unit) (return ⋆) unit 𝟏̂ₑ
                            ((unitₛ , unitₛ) , ⊩≾̂ₑ-refl))

  ex-return-is : ex-return ≡ coerce ⊩≾̂ₑ-refl (return (subV ⋆ unitₛ))
  ex-return-is = refl

  -- a variable used after time-passage: the `Et∨≾ᵘ` disjunction is `_⊩_Et∨≾ᵘ_`

  ex-var : ∅ᴴ ∣ (∅ᶜ ∷ unit) ⟨ 𝟏̂ᵣ ⟩ ⊢ᵛ⦂ unit
  ex-var = proj₁ (soundV {σ = idˢ} {Q = ∅ᴴ} ((∅ᶜ ∷ unit) ⟨ 𝟏̂ᵣ ⟩) (var zero) unit (unitₛ , et-ok unitₑ))

  ex-var-erase : ⌊ ex-var ⌋ᵛ ≡ var zero
  ex-var-erase = refl

  -- unboxing a variable: the `∃ᵗ∃ʳ` witnesses are the continuation's
  -- binder and the grade

  ex-unbox : ∅ᴴ ∣ ∅ᶜ ∷ [ 𝟏̂ᵣ ] unit ⊢ᶜ⦂ unit ! 𝟏̂ₑ
  ex-unbox = proj₁ (soundC {σ = idˢ} {Q = ∅ᴴ} (∅ᶜ ∷ [ 𝟏̂ᵣ ] unit) (unbox (var zero) (return ⋆))
                           unit 𝟏̂ₑ
                           (unit , 𝟏̂ᵣ , tt , ([ ⊩≾̂ᵣ-refl ]ₛ unitₛ , [ ⊩≾̂ᵣ-refl ]ₛ unitₛ) ,
                             ⊩≾̂ᵣ-refl ,
                             (unitₛ , unitₛ) , ⊩≾̂ₑ-refl))

  ex-unbox-erase : ⌊ ex-unbox ⌋ᶜ ≡ unbox (var zero) (return ⋆)
  ex-unbox-erase = refl

  -- unboxing an annotated variable: the annotation's atom is solved too

  ex-unbox-ann : ∅ᴴ ∣ ∅ᶜ ∷ [ 𝟏̂ᵣ ] unit ⊢ᶜ⦂ unit ! 𝟏̂ₑ
  ex-unbox-ann = proj₁ (soundC {σ = idˢ} {Q = ∅ᴴ} (∅ᶜ ∷ [ 𝟏̂ᵣ ] unit)
                               (unbox (var zero ⦂ᵛ [ 𝟏̂ᵣ ] unit) (return ⋆)) unit 𝟏̂ₑ
                               (unit , 𝟏̂ᵣ , (tt , [ ⊩≾̂ᵣ-refl ]ₛ unitₛ) ,
                                 ([ ⊩≾̂ᵣ-refl ]ₛ unitₛ , [ ⊩≾̂ᵣ-refl ]ₛ unitₛ) ,
                                 ⊩≾̂ᵣ-refl , (unitₛ , unitₛ) , ⊩≾̂ₑ-refl))

  ex-unbox-ann-erase : ⌊ ex-unbox-ann ⌋ᶜ ≡ unbox (var zero ⦂ᵛ [ 𝟏̂ᵣ ] unit) (return ⋆)
  ex-unbox-ann-erase = refl

  -- boxing a value: the `∃ᵗ` witness is the payload's type, the grade is the
  -- annotation

  ex-box : ∅ᴴ ∣ ∅ᶜ ⊢ᶜ⦂ unit ! 𝟏̂ₑ
  ex-box = proj₁ (soundC {σ = idˢ} {Q = ∅ᴴ} ∅ᶜ (box 𝟏̂ᵣ ⋆ (return ⋆)) unit 𝟏̂ₑ
                         (unit , (unitₛ , unitₛ) , (unitₛ , unitₛ) , ⊩≾̂ₑ-refl))

  ex-box-erase : ⌊ ex-box ⌋ᶜ ≡ box 𝟏̂ᵣ ⋆ (return ⋆)
  ex-box-erase = refl
