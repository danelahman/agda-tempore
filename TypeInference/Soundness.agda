------------------------------------------------------------------
-- Soundness of constraint generation                           --
--                                                              --
-- A solution of a generated constraint elaborates to a         --
-- derivation of the open calculus that erases to the raw term  --
-- it was generated from, with its annotations instantiated by  --
-- the solution (`soundV`, `soundC`).                           --
--                                                              --
-- The proof follows the soundness proof of Tavits's MSc thesis --
-- (University of Tartu, 2025).                                 --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Soundness (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades         S
open import TypeInference.OpenSyntax.Types          S
open import TypeInference.OpenSyntax.Contexts       S
open import TypeInference.OpenSyntax.ContextsLemmas S
open import TypeInference.OpenSyntax.Subst          S
open import TypeInference.OpenSyntax.Hyps           S
open import TypeInference.OpenSyntax.Language       S

open import TypeInference.Raw.Syntax S
open import TypeInference.Raw.Subst  S
open import TypeInference.Erase      S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S

open import TypeInference.Generate S

-- `TypeInference.OpenSyntax.Language` transports annotations only;
-- the clause contexts of `handle`, and every context built under a
-- generation binder, need the context transported too.

ctx-substᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ Γ' : OCtx Θ n} {A : OVType Θ}
           → Γ ≡ Γ'
           → Q ∣ Γ  ⊢V⦂ A
           ---------------
           → Q ∣ Γ' ⊢V⦂ A

ctx-substᵛ refl V = V

ctx-substᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ Γ' : OCtx Θ n} {C : OCType Θ}
           → Γ ≡ Γ'
           → Q ∣ Γ  ⊢C⦂ C
           ---------------
           → Q ∣ Γ' ⊢C⦂ C

ctx-substᶜ refl M = M

⌊ty⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A A' : OVType Θ}
     → (e : A ≡ A') → (V : Q ∣ Γ ⊢V⦂ A) → ⌊ ty-subst e V ⌋ᵛ ≡ ⌊ V ⌋ᵛ
⌊ty⌋ refl V = refl

⌊c⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C C' : OCType Θ}
    → (e : C ≡ C') → (M : Q ∣ Γ ⊢C⦂ C) → ⌊ c-subst e M ⌋ᶜ ≡ ⌊ M ⌋ᶜ
⌊c⌋ refl M = refl

⌊ctxᵛ⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ Γ' : OCtx Θ n} {A : OVType Θ}
       → (e : Γ ≡ Γ') → (V : Q ∣ Γ ⊢V⦂ A) → ⌊ ctx-substᵛ e V ⌋ᵛ ≡ ⌊ V ⌋ᵛ
⌊ctxᵛ⌋ refl V = refl

⌊ctxᶜ⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ Γ' : OCtx Θ n} {C : OCType Θ}
       → (e : Γ ≡ Γ') → (M : Q ∣ Γ ⊢C⦂ C) → ⌊ ctx-substᶜ e M ⌋ᶜ ≡ ⌊ M ⌋ᶜ
⌊ctxᶜ⌋ refl M = refl

-- Generation weakens its arguments into the scope of the `∃`s it
-- introduces; satisfaction instantiates those `∃`s by extending `σ`.
-- Each pair cancels (`wk-,*`), one lemma per binder pattern below.

-- `∃ᵗ∃ᵗ` — pairing, pattern-matching

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

-- `∃ᵗ∃ᵗ∃ᵉ` — lambda abstraction, function application

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

-- `∃ᵗ∃ᵗ∃ʳ` — unboxing

co²ᵗʳ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ') → (ρ : RExp Θ')
          → (Γ : OCtx Θ n)
          → wkʳ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ)) [ σ ,ᵗ B₁ ,ᵗ B₂ ,ʳ ρ ]ᶜᵗˣ ≡ Γ [ σ ]ᶜᵗˣ
co²ᵗʳ-ctx σ B₁ B₂ ρ Γ =
  trans (wk-,ʳ-ctx (σ ,ᵗ B₁ ,ᵗ B₂) ρ (wkᵗ-ctx (wkᵗ-ctx Γ))) (co²ᵗ-ctx σ B₁ B₂ Γ)

co²ᵗʳ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ') → (ρ : RExp Θ')
        → (A : OVType Θ)
        → wkʳ-v (wkᵗ-v (wkᵗ-v A)) [ σ ,ᵗ B₁ ,ᵗ B₂ ,ʳ ρ ]ᵛ ≡ A [ σ ]ᵛ
co²ᵗʳ-v σ B₁ B₂ ρ A =
  trans (wk-,ʳ-v (σ ,ᵗ B₁ ,ᵗ B₂) ρ (wkᵗ-v (wkᵗ-v A))) (co²ᵗ-v σ B₁ B₂ A)

co²ᵗʳ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ') → (ρ : RExp Θ')
        → (ε : EExp Θ)
        → wkʳ-e (wkᵗ-e (wkᵗ-e ε)) [ σ ,ᵗ B₁ ,ᵗ B₂ ,ʳ ρ ]ᵉ ≡ ε [ σ ]ᵉ
co²ᵗʳ-e σ B₁ B₂ ρ ε =
  trans (wk-,ʳ-e (σ ,ᵗ B₁ ,ᵗ B₂) ρ (wkᵗ-e (wkᵗ-e ε))) (co²ᵗ-e σ B₁ B₂ ε)

co²ᵗʳ-r : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ') → (ρ : RExp Θ')
        → (ρ₀ : RExp Θ)
        → wkʳ-r (wkᵗ-r (wkᵗ-r ρ₀)) [ σ ,ᵗ B₁ ,ᵗ B₂ ,ʳ ρ ]ʳ ≡ ρ₀ [ σ ]ʳ
co²ᵗʳ-r σ B₁ B₂ ρ ρ₀ =
  trans (wk-,ʳ-r (σ ,ᵗ B₁ ,ᵗ B₂) ρ (wkᵗ-r (wkᵗ-r ρ₀))) (co²ᵗ-r σ B₁ B₂ ρ₀)

-- `∃ᵗ∃ᵉ` — a prefix of the `∃ᵗ∃ᵉ∃ᵉ` pattern below

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

-- `∃ᵗ∃ᵉ∃ᵉ` — sequencing, handling

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

-- `∃ᵗ∃ᵗ∃ᵉ∃ᵉ` — handling

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

-- The interpretation of the raw term's variables, weakened under
-- the binders and composed with the extended solution, is the
-- interpretation composed with the solution.

co²ᵗ-ˢ : ∀ {Θ₀ Θ Θ'} → (ι : Subst Θ₀ Θ) → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ')
       → (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ) ⨟ˢ (σ ,ᵗ B₁ ,ᵗ B₂) ≐ˢ ι ⨟ˢ σ
co²ᵗ-ˢ ι σ B₁ B₂ = ≐ˢ-trans (wk-,ᵗ-ˢ (ι ⨟ˢ wkˢᵗ) (σ ,ᵗ B₁) B₂) (wk-,ᵗ-ˢ ι σ B₁)

co²ᵗᵉ-ˢ : ∀ {Θ₀ Θ Θ'} → (ι : Subst Θ₀ Θ) → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ')
        → (ε : EExp Θ')
        → (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ) ⨟ˢ (σ ,ᵗ B₁ ,ᵗ B₂ ,ᵉ ε) ≐ˢ ι ⨟ˢ σ
co²ᵗᵉ-ˢ ι σ B₁ B₂ ε =
  ≐ˢ-trans (wk-,ᵉ-ˢ (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ) (σ ,ᵗ B₁ ,ᵗ B₂) ε) (co²ᵗ-ˢ ι σ B₁ B₂)

co²ᵗʳ-ˢ : ∀ {Θ₀ Θ Θ'} → (ι : Subst Θ₀ Θ) → (σ : Subst Θ Θ') → (B₁ B₂ : OVType Θ')
        → (ρ : RExp Θ')
        → (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢʳ) ⨟ˢ (σ ,ᵗ B₁ ,ᵗ B₂ ,ʳ ρ) ≐ˢ ι ⨟ˢ σ
co²ᵗʳ-ˢ ι σ B₁ B₂ ρ =
  ≐ˢ-trans (wk-,ʳ-ˢ (ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ) (σ ,ᵗ B₁ ,ᵗ B₂) ρ) (co²ᵗ-ˢ ι σ B₁ B₂)

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

mutual

  soundVˢ : ∀ {Θ₀ Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
          → (ι : Subst Θ₀ Θ) → (Γ : OCtx Θ n) → (V : RawV Θ₀ n) → (A : OVType Θ)
          → σ ⊨[ Q ] genVˢ ι Γ V A
          --------------------------------------------------------------------
          → Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢V⦂ A [ σ ]ᵛ) ] (⌊ D ⌋ᵛ ≡ V [ ι ⨟ˢ σ ]ᴿᵛ)

  -- variables
  --
  -- The membership witness is `lookup-var` in the substituted context, so
  -- its position is `i` on the nose; the `Et∨≾ᵘ` conjunct is `VarOK`
  -- once the type and the grade are aligned, and the subtyping atom is
  -- the `subV` that carries the declared type to the expected one.

  soundVˢ {σ = σ} {Q = Q} ι Γ (var i) A (st , ok) =
    subV D₀ st' , cong var (var-pos-lookup (Γ [ σ ]ᶜᵗˣ) i)
    where
      x = lookup-var (Γ [ σ ]ᶜᵗˣ) i

      ok₁ = subst₂ (VarOK Q)
                   (sym (lookup-ty-subst Γ σ i))
                   (sym (lookup-gr-subst Γ σ i))
                   ok

      D₀ = var x ok₁

      st' = subst (λ z → Q ∣ z <:̂ᵛ A [ σ ]ᵛ) (sym (lookup-ty-subst Γ σ i)) st

  -- base-typed constants, unit, booleans

  --
  -- The first half of the type equation is the `subV` into the expected
  -- type.

  soundVˢ ι Γ (const B c) A (st , _) = subV (const B c) st , refl
  soundVˢ ι Γ ⋆           A (st , _) = subV ⋆ st           , refl
  soundVˢ ι Γ true        A (st , _) = subV true st        , refl
  soundVˢ ι Γ false       A (st , _) = subV false st       , refl

  -- natural numbers

  soundVˢ ι Γ zero        A (st , _) = subV zero st        , refl
  soundVˢ ι Γ (succ V)    A ((st , _) , s) =
    subV (succ (proj₁ ih)) st , cong succ (proj₂ ih)
    where
      ih = soundVˢ ι Γ V Nat s

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

      D = subV ⦉ D₁ , D₂ ⦊ (subst (λ z → Q ∣ _ <:̂ᵛ z) pA st)

      q = cong₂ ⦉_,_⦊
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᵛ pι V₁)))
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₂)) (trans (proj₂ ih₂) ([≐]ᴿᵛ pι V₂)))

  -- lambda abstraction

  soundVˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (lam M) A (B₁ , B₂ , ε , st , s) =
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

      D = subV (lam D₀) (subst (λ z → Q ∣ _ <:̂ᵛ z) pA st)

      q = cong lam (trans (⌊ctxᶜ⌋ (cong (_∷ _) pΓ) (proj₁ ih))
                          (trans (proj₂ ih) ([≐]ᴿᶜ pι M)))

  -- type annotation
  --
  -- The recording rule at the instantiated annotation, then the subtyping
  -- atom as a `subV`.

  soundVˢ {σ = σ} ι Γ (V ⦂ᵛ B) A (s , st) =
    subV (annᵛ (B [ ι ]ᵛ [ σ ]ᵛ) (proj₁ ih)) st ,
    cong₂ _⦂ᵛ_ (proj₂ ih) ([⨟]ᵛ B ι σ)
    where
      ih = soundVˢ ι Γ V (B [ ι ]ᵛ) s


  soundCˢ : ∀ {Θ₀ Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
          → (ι : Subst Θ₀ Θ) → (Γ : OCtx Θ n) → (M : RawC Θ₀ n)
          → (A : OVType Θ) → (t : EExp Θ)
          → σ ⊨[ Q ] genCˢ ι Γ M (A ‼ t)
          ---------------------------------------------------------------------
          → Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢C⦂ A [ σ ]ᵛ ‼ t [ σ ]ᵉ) ]
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
      D₂ = c-subst (cong (_‼ _) pA) (ctx-substᶜ c₂ (proj₁ ih₂))

      D = coerce (subst (λ x → Q ⊩ _ ≾̂ₑ x) pt le) (D₁ ⨟ D₂)

      q = cong₂ _⨟_
                (trans (⌊ctxᶜ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᶜ pι M₁)))
                (trans (⌊c⌋ (cong (_‼ _) pA) (ctx-substᶜ c₂ (proj₁ ih₂)))
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

      ih₁ = soundVˢ ι↑ Γ↑ V₁ (α ⇒ (β ‼ e)) s₁
      ih₂ = soundVˢ ι↑ Γ↑ V₂ α s₂

      D₁ = ctx-substᵛ pΓ (proj₁ ih₁)
      D₂ = ctx-substᵛ pΓ (proj₁ ih₂)

      D = subC (D₁ · D₂)
               (subst (λ z → Q ∣ _ <:̂ᵛ z) pA st
                  ‼ₛ subst (λ z → Q ⊩ _ ≾̂ₑ z) pt le)

      q = cong₂ _·_
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᵛ pι V₁)))
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₂)) (trans (proj₂ ih₂) ([≐]ᴿᵛ pι V₂)))

  -- pattern-matching

  soundCˢ {Θ = Θ} {σ = σ} ι Γ (match V `in M) A t (B₁ , B₂ , s₁ , s₂) =
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
      D₂ = c-subst (cong₂ _‼_ pA pt) (ctx-substᶜ c₂ (proj₁ ih₂))

      D = match D₁ `in D₂

      q = cong₂ match_`in_
                (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᵛ pι V)))
                (trans (⌊c⌋ (cong₂ _‼_ pA pt) (ctx-substᶜ c₂ (proj₁ ih₂)))
                       (trans (⌊ctxᶜ⌋ c₂ (proj₁ ih₂))
                              (trans (proj₂ ih₂) ([≐]ᴿᶜ pι M))))

  -- empty type elimination

  soundCˢ ι Γ (absurd V) A t s =
    absurd (proj₁ ih) , cong absurd (proj₂ ih)
    where
      ih = soundVˢ ι Γ V Empty s

  -- boolean elimination

  soundCˢ ι Γ (if V `then M₁ `else M₂) A t (s₀ , s₁ , s₂) =
    if (proj₁ ih₀) `then (proj₁ ih₁) `else (proj₁ ih₂) ,
    cong₃ if_`then_`else_ (proj₂ ih₀) (proj₂ ih₁) (proj₂ ih₂)
    where
      ih₀ = soundVˢ ι Γ V Bool s₀
      ih₁ = soundCˢ ι Γ M₁ A t s₁
      ih₂ = soundCˢ ι Γ M₂ A t s₂

  -- natural-number elimination

  soundCˢ ι Γ (caseℕ V `zero M₁ `succ M₂) A t (s₀ , s₁ , s₂) =
    caseℕ (proj₁ ih₀) `zero (proj₁ ih₁) `succ (proj₁ ih₂) ,
    cong₃ caseℕ_`zero_`succ_ (proj₂ ih₀) (proj₂ ih₁) (proj₂ ih₂)
    where
      ih₀ = soundVˢ ι Γ V Nat s₀
      ih₁ = soundCˢ ι Γ M₁ A t s₁
      ih₂ = soundCˢ ι (Γ ∷ Nat) M₂ A t s₂

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
      ih₂ = soundCˢ ι↑ (Γ↑ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ) M A↑ e s₂

      c₂ = cong₂ (λ Γ₀ A₀ → Γ₀ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ A₀) pΓ pa

      D₁ = ty-subst pp (ctx-substᵛ pΓ (proj₁ ih₁))
      D₂ = c-subst (cong (_‼ _) pA) (ctx-substᶜ c₂ (proj₁ ih₂))

      D = coerce (subst (λ x → Q ⊩ _ ≾̂ₑ x) pt le) (perform op D₁ D₂)

      q = cong₂ (perform op)
                (trans (⌊ty⌋ pp (ctx-substᵛ pΓ (proj₁ ih₁)))
                       (trans (⌊ctxᵛ⌋ pΓ (proj₁ ih₁))
                              (trans (proj₂ ih₁) ([≐]ᴿᵛ pι V))))
                (trans (⌊c⌋ (cong (_‼ _) pA) (ctx-substᶜ c₂ (proj₁ ih₂)))
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

      ih = soundCˢ ι↑ (Γ↑ ⟨ rconst (of-durʳ τ) ⟩) M A↑ e s

      c₀ = cong (_⟨ rconst (of-durʳ τ) ⟩) pΓ

      D₀ = c-subst (cong (_‼ _) pA) (ctx-substᶜ c₀ (proj₁ ih))

      D = coerce (subst (λ x → Q ⊩ _ ≾̂ₑ x) pt le) (delay τ D₀)

      q = cong (delay τ)
               (trans (⌊c⌋ (cong (_‼ _) pA) (ctx-substᶜ c₀ (proj₁ ih)))
                      (trans (⌊ctxᶜ⌋ c₀ (proj₁ ih))
                             (trans (proj₂ ih) ([≐]ᴿᶜ pι M))))

  -- effect handling
  --
  -- The clause family is typed one `∀ᵉ` deeper; the clause equalities
  -- hold pointwise, so the erasure of the family needs `fun-ext`.

  soundCˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (handle M `with H `in N) A t
          (B₁ , B₂ , ε₁ , ε₂ , s₁ , s₂ , st , le , cls) =
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
      pt  = co²ᵗ²ᵉ-e    σ B₁ B₂ ε₁ ε₂ t
      pΓ⇑ = co²ᵗ²ᵉ-ctx↑ σ B₁ B₂ ε₁ ε₂ Γ
      pγ⇑ = wk-↑ᵉ-v σ' γ
      pι  = co²ᵗ²ᵉ-ˢ    ι σ B₁ B₂ ε₁ ε₂
      pι⇑ = co²ᵗ²ᵉ-ˢ↑   ι σ B₁ B₂ ε₁ ε₂

      ih₁ = soundCˢ ι↑ Γ↑ M α e₁ s₁
      ih₂ = soundCˢ ι↑ (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) N γ e₂ s₂

      c₂ = cong (λ Γ₀ → Γ₀ ⟨ ∣ ε₁ ∣̂ᵉ ⟩ ∷ B₁) pΓ

      D₁ = ctx-substᶜ pΓ (proj₁ ih₁)
      D₂ = ctx-substᶜ c₂ (proj₁ ih₂)

      ihH : (op : Op) → _
      ihH op =
        soundCˢ (ι↑ ↑ᵉ)
                (Γ⇑ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                    ∷ [ rconst (mapᵉ (op-grade op)) ] (⌜ arity op ⌝ᵍ ⇒ γ⇑ ‼ e''))
                (H op) γ⇑ (econst (op-grade op) ·̂ₑ e'') (cls op)

      cH : (op : Op) → _
      cH op =
        cong₂ _∷_
              (cong₂ _∷_ (cong (_⟨ rconst ⊤ᵣ ⟩) pΓ⇑) (⌜⌝ᵍ-subst (σ' ↑ᵉ) (param op)))
              (cong₂ (λ A₀ B₀ → [ rconst (mapᵉ (op-grade op)) ] (A₀ ⇒ B₀ ‼ _))
                     (⌜⌝ᵍ-subst (σ' ↑ᵉ) (arity op))
                     pγ⇑)

      DH : (op : Op) → _
      DH op = c-subst (cong (_‼ _) pγ⇑) (ctx-substᶜ (cH op) (proj₁ (ihH op)))

      D = subC (handle D₁ `with DH `in D₂)
               (subst (λ z → Q ∣ _ <:̂ᵛ z) pA st
                  ‼ₛ subst (λ z → Q ⊩ _ ≾̂ₑ z) pt le)

      q = cong₃ (λ x y z → handle x `with y `in z)
                (trans (⌊ctxᶜ⌋ pΓ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᶜ pι M)))
                (fun-ext (λ op →
                   trans (⌊c⌋ (cong (_‼ _) pγ⇑) (ctx-substᶜ (cH op) (proj₁ (ihH op))))
                         (trans (⌊ctxᶜ⌋ (cH op) (proj₁ (ihH op)))
                                (trans (proj₂ (ihH op)) ([≐]ᴿᶜ pι⇑ (H op))))))
                (trans (⌊ctxᶜ⌋ c₂ (proj₁ ih₂)) (trans (proj₂ ih₂) ([≐]ᴿᶜ pι N)))

  -- unboxing a boxed variable

  soundCˢ {Θ = Θ} {σ = σ} {Q = Q} ι Γ (unbox i N) A t (B₁ , B₂ , ρ , (sb , _) , le , st , s') =
    D , q
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢʳ
      σ' = σ ,ᵗ B₁ ,ᵗ B₂ ,ʳ ρ
      Γ↑ = wkʳ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))
      A↑ = wkʳ-v (wkᵗ-v (wkᵗ-v A))
      t↑ = wkʳ-e (wkᵗ-e (wkᵗ-e t))
      β  = wkʳ-v (tvar (newᵗ {Θ +ty}))

      pΓ = co²ᵗʳ-ctx σ B₁ B₂ ρ Γ
      pA = co²ᵗʳ-v   σ B₁ B₂ ρ A
      pt = co²ᵗʳ-e   σ B₁ B₂ ρ t
      pι = co²ᵗʳ-ˢ   ι σ B₁ B₂ ρ

      -- the `∃ᵗ`-bound variables are the payload `B₁` and the binder `B₂`

      pα = trans (wk-,ʳ-v (σ ,ᵗ B₁ ,ᵗ B₂) ρ (wkᵗ-v (tvar (newᵗ {Θ}))))
                 (wk-,ᵗ-v (σ ,ᵗ B₁) B₂ (tvar (newᵗ {Θ})))

      pβ = wk-,ʳ-v (σ ,ᵗ B₁ ,ᵗ B₂) ρ (tvar (newᵗ {Θ +ty}))

      -- lookup in the weakened context, instantiated, is lookup in the
      -- substituted one

      lty = trans (cong (_[ σ' ]ᵛ)
                        (trans (lookup-ty-wkʳ (wkᵗ-ctx (wkᵗ-ctx Γ)) i)
                               (cong wkʳ-v
                                     (trans (lookup-ty-wkᵗ (wkᵗ-ctx Γ) i)
                                            (cong wkᵗ-v (lookup-ty-wkᵗ Γ i))))))
                  (trans (co²ᵗʳ-v σ B₁ B₂ ρ (lookup-ty Γ i))
                         (sym (lookup-ty-subst Γ σ i)))

      lgr = trans (cong (_[ σ' ]ʳ)
                        (trans (lookup-gr-wkʳ (wkᵗ-ctx (wkᵗ-ctx Γ)) i)
                               (cong wkʳ-r
                                     (trans (lookup-gr-wkᵗ (wkᵗ-ctx Γ) i)
                                            (cong wkᵗ-r (lookup-gr-wkᵗ Γ i))))))
                  (trans (co²ᵗʳ-r σ B₁ B₂ ρ (lookup-gr Γ i))
                         (sym (lookup-gr-subst Γ σ i)))

      -- the looked-up type is a subtype of the box type, so a box type
      -- whose grade is above and whose payload is below

      sb' = subst₂ (Q ∣_<:̂ᵛ_) lty (cong [ ρ ]_ pα) sb

      bx  = <:̂ᵛ-boxʳ sb'
      ρ₀  = proj₁ bx
      A₀  = proj₁ (proj₂ bx)
      eq' = proj₁ (proj₂ (proj₂ bx))
      gr  = proj₁ (proj₂ (proj₂ (proj₂ bx)))
      ty  = proj₂ (proj₂ (proj₂ (proj₂ bx)))

      x = ∈̂-ty-subst eq' (lookup-var (Γ [ σ ]ᶜᵗˣ) i)

      ok = transᵣ (subst (λ z → Q ⊩ z ≾̂ᵣ ρ) lgr le) gr

      ih = soundCˢ ι↑ (Γ↑ ∷ β) N A↑ t↑ s'

      c₀ = cong₂ _∷_ pΓ pβ

      D₀ = c-subst (cong₂ _‼_ pA pt) (ctx-substᶜ c₀ (proj₁ ih))

      D = unbox x ok (<:̂ᵛ-trans ty (subst₂ (Q ∣_<:̂ᵛ_) pα pβ st)) D₀

      q = cong₂ unbox
                (trans (var-pos-ty-subst eq' (lookup-var (Γ [ σ ]ᶜᵗˣ) i))
                       (var-pos-lookup (Γ [ σ ]ᶜᵗˣ) i))
                (trans (⌊c⌋ (cong₂ _‼_ pA pt) (ctx-substᶜ c₀ (proj₁ ih)))
                       (trans (⌊ctxᶜ⌋ c₀ (proj₁ ih))
                              (trans (proj₂ ih) ([≐]ᴿᶜ pι N))))

  -- boxing up a value
  --
  -- The grade is the annotation, instantiated; only the payload's type is
  -- a witness.

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
      D₂ = c-subst (cong₂ _‼_ pA pt) (ctx-substᶜ c₂ (proj₁ ih₂))

      D = box ρ' D₁ D₂

      q = cong₂ (box ρ')
                (trans (⌊ctxᵛ⌋ c₁ (proj₁ ih₁)) (trans (proj₂ ih₁) ([≐]ᴿᵛ pι V)))
                (trans (⌊c⌋ (cong₂ _‼_ pA pt) (ctx-substᶜ c₂ (proj₁ ih₂)))
                       (trans (⌊ctxᶜ⌋ c₂ (proj₁ ih₂))
                              (trans (proj₂ ih₂) ([≐]ᴿᶜ pι N))))

  -- type annotation
  --
  -- As for values, the two atoms making up the `subC`.

  soundCˢ {σ = σ} ι Γ (M ⦂ᶜ (B ‼ u)) A t (s , st , le) =
    subC (annᶜ (B [ ι ]ᵛ [ σ ]ᵛ ‼ u [ ι ]ᵉ [ σ ]ᵉ) (proj₁ ih)) (st ‼ₛ le) ,
    cong₂ _⦂ᶜ_ (proj₂ ih) ([⨟]ᶜ (B ‼ u) ι σ)
    where
      ih = soundCˢ ι Γ M (B [ ι ]ᵛ) (u [ ι ]ᵉ) s

-- Generation for a raw term over the scope of the context: the program's
-- annotations are instantiated by the solution.

soundV : ∀ {Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
       → (Γ : OCtx Θ n) → (V : RawV Θ n) → (A : OVType Θ)
       → σ ⊨[ Q ] genV Γ V A
       --------------------------------------------------------------
       → Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢V⦂ A [ σ ]ᵛ) ] (⌊ D ⌋ᵛ ≡ V [ σ ]ᴿᵛ)

soundV {σ = σ} Γ V A s =
  proj₁ ih , trans (proj₂ ih) ([≐]ᴿᵛ (⨟-idˡ σ) V)
  where
    ih = soundVˢ idˢ Γ V A s

soundC : ∀ {Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
       → (Γ : OCtx Θ n) → (M : RawC Θ n) → (A : OVType Θ) → (t : EExp Θ)
       → σ ⊨[ Q ] genC Γ M (A ‼ t)
       -----------------------------------------------------------------------
       → Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢C⦂ A [ σ ]ᵛ ‼ t [ σ ]ᵉ) ] (⌊ D ⌋ᶜ ≡ M [ σ ]ᴿᶜ)

soundC {σ = σ} Γ M A t s =
  proj₁ ih , trans (proj₂ ih) ([≐]ᴿᶜ (⨟-idˡ σ) M)
  where
    ih = soundCˢ idˢ Γ M A t s

-- Sanity checks: four closed examples, solved by the identity
-- substitution and the empty hypothesis set, elaborated and erased
-- back.

private

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  -- returning a value: the `≾̂ₑᶜ` conjunct becomes a `coerce`, the type
  -- equation's first half a `subV`

  ex-return : ∅ᴴ ∣ ∅ᶜ ∷ Unit ⊢C⦂ Unit ‼ ûₑ
  ex-return = proj₁ (soundC {σ = idˢ} {Q = ∅ᴴ} (∅ᶜ ∷ Unit) (return ⋆) Unit ûₑ
                            ((Unitₛ , Unitₛ) , ⊩≾̂ₑ-refl))

  ex-return-is : ex-return ≡ coerce ⊩≾̂ₑ-refl (return (subV ⋆ Unitₛ))
  ex-return-is = refl

  -- a variable used after time-passage: the `Et∨≾ᵘ` disjunction is `VarOK`

  ex-var : ∅ᴴ ∣ (∅ᶜ ∷ Unit) ⟨ ûᵣ ⟩ ⊢V⦂ Unit
  ex-var = proj₁ (soundV {σ = idˢ} {Q = ∅ᴴ} ((∅ᶜ ∷ Unit) ⟨ ûᵣ ⟩) (var zero) Unit (Unitₛ , et-ok Unitₑ))

  ex-var-erase : ⌊ ex-var ⌋ᵛ ≡ var zero
  ex-var-erase = refl

  -- unboxing a boxed variable: the `∃ᵗ∃ᵗ∃ʳ` witnesses are the payload, the
  -- continuation's binder, and the grade

  ex-unbox : ∅ᴴ ∣ ∅ᶜ ∷ [ ûᵣ ] Unit ⊢C⦂ Unit ‼ ûₑ
  ex-unbox = proj₁ (soundC {σ = idˢ} {Q = ∅ᴴ} (∅ᶜ ∷ [ ûᵣ ] Unit) (unbox zero (return ⋆)) Unit ûₑ
                           (Unit , Unit , ûᵣ , ([ ⊩≾̂ᵣ-refl ]ₛ Unitₛ , [ ⊩≾̂ᵣ-refl ]ₛ Unitₛ) , ⊩≾̂ᵣ-refl ,
                             Unitₛ , (Unitₛ , Unitₛ) , ⊩≾̂ₑ-refl))

  ex-unbox-erase : ⌊ ex-unbox ⌋ᶜ ≡ unbox zero (return ⋆)
  ex-unbox-erase = refl

  -- boxing a value: the `∃ᵗ` witness is the payload's type, the grade is the
  -- annotation

  ex-box : ∅ᴴ ∣ ∅ᶜ ⊢C⦂ Unit ‼ ûₑ
  ex-box = proj₁ (soundC {σ = idˢ} {Q = ∅ᴴ} ∅ᶜ (box ûᵣ ⋆ (return ⋆)) Unit ûₑ
                         (Unit , (Unitₛ , Unitₛ) , (Unitₛ , Unitₛ) , ⊩≾̂ₑ-refl))

  ex-box-erase : ⌊ ex-box ⌋ᶜ ≡ box ûᵣ ⋆ (return ⋆)
  ex-box-erase = refl
