------------------------------------------------------------------
-- Substitution of the definitions of a program context         --
--                                                              --
-- Given, for each definition of the program context of `Γ`, a  --
-- closed typing of a run-time value at its scheme (`DefsEnv`), --
-- a typing in `Γ` gives one in `local Γ`, the context without  --
-- its program context (`sdef-v`, `sdef-c`): each use of a      --
-- definition at an instance `δ` is the definition's typing     --
-- instantiated at `δ`, which the hypotheses of the use entail. --
-- The erasure is the run-time substitution of the definitions  --
-- (`∥sdef-v∥`, `∥sdef-c∥`).                                    --
------------------------------------------------------------------

open import Data.Fin using (Fin; suc)
open import Data.Maybe.Base using (just; maybe′)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Programs.Substitution (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OpenCalculus.Syntax.Grades            S
open import OpenCalculus.Syntax.Types             S
open import OpenCalculus.Syntax.Contexts          S
open import OpenCalculus.Syntax.Subst             S
open import OpenCalculus.Hypotheses               S
open import OpenCalculus.Typing                   S
open import OpenCalculus.Typing.Erasure           S
open import OpenCalculus.Typing.Transport         S
open import OpenCalculus.Typing.Renaming          S
open import OpenCalculus.Typing.GradeSubstitution S
open import OpenCalculus.Syntax.Run               S
open import OpenCalculus.Programs.Syntax          S

------------------------------------------------------------------------
-- The context without its program context

local : ∀ {Θ n} → OCtx Θ n → OCtx Θ n
local []        = []
local (Δ ▶ s)   = []
local (Γ ∷ A)   = local Γ ∷ A
local (Γ ⟨ ρ ⟩) = local Γ ⟨ ρ ⟩

defs-local : ∀ {Θ n} → (Γ : OCtx Θ n) → defs (local Γ) ≡ ∅ᵖ
defs-local []        = refl
defs-local (Δ ▶ s)   = refl
defs-local (Γ ∷ A)   = defs-local Γ
defs-local (Γ ⟨ ρ ⟩) = defs-local Γ

local-wkᵉ : ∀ {Θ n} → (Γ : OCtx Θ n) → local (wkᵉ-ctx Γ) ≡ wkᵉ-ctx (local Γ)
local-wkᵉ []        = refl
local-wkᵉ (Δ ▶ s)   = refl
local-wkᵉ (Γ ∷ A)   = cong (_∷ wkᵉ-v A) (local-wkᵉ Γ)
local-wkᵉ (Γ ⟨ ρ ⟩) = cong (_⟨ wkᵉ-r ρ ⟩) (local-wkᵉ Γ)

local-⌜⌝ : ∀ {Θ} → (Δ : PCtx) → local (⌜_⌝ᵖ {Θ} Δ) ≡ []
local-⌜⌝ ∅ᵖ       = refl
local-⌜⌝ (Δ ∷ᵖ s) = refl

∈̂-local : ∀ {Θ n} {A : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n} → A ∈̂[ ρ ] Γ → A ∈̂[ ρ ] local Γ
∈̂-local Hd        = Hd
∈̂-local (Tl-∷ x)  = Tl-∷ (∈̂-local x)
∈̂-local (Tl-⟨⟩ x) = Tl-⟨⟩ (∈̂-local x)

var-pos-local : ∀ {Θ n} {A : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
              → (x : A ∈̂[ ρ ] Γ) → var-pos (∈̂-local x) ≡ var-pos x
var-pos-local Hd        = refl
var-pos-local (Tl-∷ x)  = cong suc (var-pos-local x)
var-pos-local (Tl-⟨⟩ x) = var-pos-local x

-- The empty context renames into a context without definitions

ren₀ : ∀ {Θ n} {Q : Hyps Θ} → (Γ : OCtx Θ n) → Ren Q [] (local Γ)
pos (ren₀ Γ) = from0
ty  (ren₀ Γ) ()
gr  (ren₀ Γ) ()
dfs (ren₀ Γ) = defs-local Γ

------------------------------------------------------------------------
-- Closed typings of the definitions

-- For each definition of `Δ`, a typing at its scheme, in the empty
-- context, of the value `ρ` gives it

record DefsEnv (ρ : Defs) (Δ : PCtx) : Set where
  constructor defsEnv
  field
    closed : ∀ {s k} → s ∈ᵖ[ k ] Δ
           → Σ[ D ∈ (Qˢ s ∣ [] ⊢V⦂ Xˢ s) ] (ρ k ≡ just ∥ D ∥ᵛ)

open DefsEnv public

------------------------------------------------------------------------
-- The substitution lemma

private

  clause-local : ∀ {Θ n} → (Γ : OCtx Θ n) → (B : OVType Θ) → (op : Op)
               → local (clause-ctx Γ B op) ≡ clause-ctx (local Γ) B op
  clause-local {Θ} Γ B op =
    cong (λ G → G ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                  ∷ [ rconst (mapᵉ (op-grade op)) ] (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ})))
         (local-wkᵉ Γ)

  env-wkᵉ : ∀ {Θ n} {ρ : Defs} → (Γ : OCtx Θ n) → DefsEnv ρ (defs Γ)
          → DefsEnv ρ (defs (wkᵉ-ctx Γ))
  env-wkᵉ Γ r = subst (DefsEnv _) (sym (defs-wkᵉ Γ)) r

  -- the definition used, instantiated, in the context without
  -- definitions

  use : ∀ {Θ n} {Q : Hyps Θ} (Γ : OCtx Θ n) {ρ : Defs} {s k}
      → DefsEnv ρ (defs Γ) → s ∈ᵖ[ k ] defs Γ → (δ : Subst (Θˢ s) Θ) → Q ⊩ᴴ Qˢ s [ δ ]
      → Q ∣ local Γ ⊢V⦂ Xˢ s [ δ ]ᵛ
  use Γ r f δ h = rename-v (ren₀ Γ) (substᵛ δ h (proj₁ (closed r f)))

  ∥use∥ : ∀ {Θ n} {Q : Hyps Θ} (Γ : OCtx Θ n) {ρ : Defs} {s k}
        → (r : DefsEnv ρ (defs Γ)) → (f : s ∈ᵖ[ k ] defs Γ) → (δ : Subst (Θˢ s) Θ)
        → (h : Q ⊩ᴴ Qˢ s [ δ ])
        → ∥ use Γ r f δ h ∥ᵛ ≡ def k [ ρ ]ᵈᵛ
  ∥use∥ Γ {k = k} r f δ h =
    trans (∥rename-v∥ (ren₀ Γ) (substᵛ δ h D₀))
      (trans (cong wk₀ (trans (cong eraseᵛ (⌊substᵛ⌋ δ h D₀)) (erase-substᵛ ⌊ D₀ ⌋ᵛ δ)))
             (cong (maybe′ wk₀ (def k)) (sym (proj₂ (closed r f)))))
    where D₀ = proj₁ (closed r f)

mutual

  sdef-v : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ} {ρ : Defs}
         → DefsEnv ρ (defs Γ) → Q ∣ Γ ⊢V⦂ A → Q ∣ local Γ ⊢V⦂ A
  sdef-v r (var x p)       = var (∈̂-local x) p
  sdef-v {Γ = Γ} r (def f δ h e) = ty-subst (sym e) (use Γ r f δ h)
  sdef-v r (const B c)     = const B c
  sdef-v r ⋆               = ⋆
  sdef-v r true            = true
  sdef-v r false           = false
  sdef-v r zero            = zero
  sdef-v r (succ V)        = succ (sdef-v r V)
  sdef-v r ⦉ V , W ⦊        = ⦉ sdef-v r V , sdef-v r W ⦊
  sdef-v r (inl V)         = inl (sdef-v r V)
  sdef-v r (inr V)         = inr (sdef-v r V)
  sdef-v r nil             = nil
  sdef-v r (cons V W)      = cons (sdef-v r V) (sdef-v r W)
  sdef-v r (cmp ⋈ V W et)  = cmp ⋈ (sdef-v r V) (sdef-v r W) et
  sdef-v r (lam M)         = lam (sdef-c r M)
  sdef-v {Γ = Γ} r (handler {B = B} N H) =
    handler (sdef-c r N)
            (λ op → ctx-castᶜ (clause-local Γ B op) (sdef-c (env-wkᵉ Γ r) (H op)))
  sdef-v r (annᵛ A V)      = annᵛ A (sdef-v r V)
  sdef-v r (subV V p)      = subV (sdef-v r V) p

  sdef-c : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ} {ρ : Defs}
         → DefsEnv ρ (defs Γ) → Q ∣ Γ ⊢C⦂ C → Q ∣ local Γ ⊢C⦂ C
  sdef-c r (return V)                = return (sdef-v r V)
  sdef-c r (M ⨟ N)                   = sdef-c r M ⨟ sdef-c r N
  sdef-c r (V · W)                   = sdef-v r V · sdef-v r W
  sdef-c r (match V `in M)           = match sdef-v r V `in sdef-c r M
  sdef-c r (absurd V)                = absurd (sdef-v r V)
  sdef-c r (if V `then M `else N)    = if sdef-v r V `then sdef-c r M `else sdef-c r N
  sdef-c r (caseℕ V `zero M `succ N) = caseℕ sdef-v r V `zero sdef-c r M `succ sdef-c r N
  sdef-c r (case+ V `inl M `inr N)   = case+ sdef-v r V `inl sdef-c r M `inr sdef-c r N
  sdef-c r (caseL V `nil M `cons N)  = caseL sdef-v r V `nil sdef-c r M `cons sdef-c r N
  sdef-c r (recℕ V M N p)            = recℕ (sdef-v r V) (sdef-c r M) (sdef-c r N) p
  sdef-c r (recL V M N p)            = recL (sdef-v r V) (sdef-c r M) (sdef-c r N) p
  sdef-c r (perform op V M)          = perform op (sdef-v r V) (sdef-c r M)
  sdef-c r (delay τ M)               = delay τ (sdef-c r M)
  sdef-c r (handle M `with V)        = handle sdef-c r M `with sdef-v r V
  sdef-c r (unbox {z = z} R p N)    = unbox (res-move (∈̂-local z) R) p (sdef-c r N)
  sdef-c r (box ρ V N)               = box ρ (sdef-v r V) (sdef-c r N)
  sdef-c r (annᶜ C M)                = annᶜ C (sdef-c r M)
  sdef-c r (subC M p)                = subC (sdef-c r M) p

-- The erasure of the substituted derivation substitutes the
-- definitions in the erasure

mutual

  ∥sdef-v∥ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ} {ρ : Defs}
           → (r : DefsEnv ρ (defs Γ)) → (V : Q ∣ Γ ⊢V⦂ A)
           → ∥ sdef-v r V ∥ᵛ ≡ ∥ V ∥ᵛ [ ρ ]ᵈᵛ
  ∥sdef-v∥ r (var x p)       = cong var (var-pos-local x)
  ∥sdef-v∥ {Γ = Γ} r (def f δ h e) =
    trans (cong eraseᵛ (⌊ty-subst⌋ (sym e) _)) (∥use∥ Γ r f δ h)
  ∥sdef-v∥ r (const B c)     = refl
  ∥sdef-v∥ r ⋆               = refl
  ∥sdef-v∥ r true            = refl
  ∥sdef-v∥ r false           = refl
  ∥sdef-v∥ r zero            = refl
  ∥sdef-v∥ r (succ V)        = cong succ (∥sdef-v∥ r V)
  ∥sdef-v∥ r ⦉ V , W ⦊        = cong₂ ⦉_,_⦊ (∥sdef-v∥ r V) (∥sdef-v∥ r W)
  ∥sdef-v∥ r (inl V)         = cong inl (∥sdef-v∥ r V)
  ∥sdef-v∥ r (inr V)         = cong inr (∥sdef-v∥ r V)
  ∥sdef-v∥ r nil             = refl
  ∥sdef-v∥ r (cons V W)      = cong₂ cons (∥sdef-v∥ r V) (∥sdef-v∥ r W)
  ∥sdef-v∥ r (cmp ⋈ V W et)  = cong₂ (cmp ⋈) (∥sdef-v∥ r V) (∥sdef-v∥ r W)
  ∥sdef-v∥ r (lam M)         = cong lam (∥sdef-c∥ r M)
  ∥sdef-v∥ {Γ = Γ} r (handler {B = B} N H) =
    cong₂ handler (∥sdef-c∥ r N)
          (fun-ext (λ op → trans (cong eraseᶜ (⌊ctx-castᶜ⌋ (clause-local Γ B op) _))
                                 (∥sdef-c∥ (env-wkᵉ Γ r) (H op))))
  ∥sdef-v∥ r (annᵛ A V)      = ∥sdef-v∥ r V
  ∥sdef-v∥ r (subV V p)      = ∥sdef-v∥ r V

  ∥sdef-c∥ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ} {ρ : Defs}
           → (r : DefsEnv ρ (defs Γ)) → (M : Q ∣ Γ ⊢C⦂ C)
           → ∥ sdef-c r M ∥ᶜ ≡ ∥ M ∥ᶜ [ ρ ]ᵈᶜ
  ∥sdef-c∥ r (return V)                = cong return (∥sdef-v∥ r V)
  ∥sdef-c∥ r (M ⨟ N)                   = cong₂ _⨟_ (∥sdef-c∥ r M) (∥sdef-c∥ r N)
  ∥sdef-c∥ r (V · W)                   = cong₂ _·_ (∥sdef-v∥ r V) (∥sdef-v∥ r W)
  ∥sdef-c∥ r (match V `in M)           = cong₂ match_`in_ (∥sdef-v∥ r V) (∥sdef-c∥ r M)
  ∥sdef-c∥ r (absurd V)                = cong absurd (∥sdef-v∥ r V)
  ∥sdef-c∥ r (if V `then M `else N)    =
    cong₃ if_`then_`else_ (∥sdef-v∥ r V) (∥sdef-c∥ r M) (∥sdef-c∥ r N)
  ∥sdef-c∥ r (caseℕ V `zero M `succ N) =
    cong₃ caseℕ_`zero_`succ_ (∥sdef-v∥ r V) (∥sdef-c∥ r M) (∥sdef-c∥ r N)
  ∥sdef-c∥ r (case+ V `inl M `inr N)   =
    cong₃ case+_`inl_`inr_ (∥sdef-v∥ r V) (∥sdef-c∥ r M) (∥sdef-c∥ r N)
  ∥sdef-c∥ r (caseL V `nil M `cons N)  =
    cong₃ caseL_`nil_`cons_ (∥sdef-v∥ r V) (∥sdef-c∥ r M) (∥sdef-c∥ r N)
  ∥sdef-c∥ r (recℕ V M N p)            = cong₃ recℕ (∥sdef-v∥ r V) (∥sdef-c∥ r M) (∥sdef-c∥ r N)
  ∥sdef-c∥ r (recL V M N p)            = cong₃ recL (∥sdef-v∥ r V) (∥sdef-c∥ r M) (∥sdef-c∥ r N)
  ∥sdef-c∥ r (perform op V M)          = cong₂ (perform op) (∥sdef-v∥ r V) (∥sdef-c∥ r M)
  ∥sdef-c∥ r (delay τ M)               = cong (delay τ) (∥sdef-c∥ r M)
  ∥sdef-c∥ r (handle M `with V)        = cong₂ handle_`with_ (∥sdef-c∥ r M) (∥sdef-v∥ r V)
  ∥sdef-c∥ r (unbox {z = z} R p N)    =
    cong₂ unbox (trans (∥res∥ (res-move (∈̂-local z) R))
                       (trans (cong var (var-pos-local z)) (cong (_[ _ ]ᵈᵛ) (sym (∥res∥ R)))))
                (∥sdef-c∥ r N)
  ∥sdef-c∥ r (box ρ V N)               = cong₂ box (∥sdef-v∥ r V) (∥sdef-c∥ r N)
  ∥sdef-c∥ r (annᶜ C M)                = ∥sdef-c∥ r M
  ∥sdef-c∥ r (subC M p)                = ∥sdef-c∥ r M
