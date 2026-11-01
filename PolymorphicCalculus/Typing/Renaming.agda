------------------------------------------------------------------
-- Renaming of term variables in open derivations               --
--                                                              --
-- A renaming `Ren Q Γ Γ'` sends each variable of `Γ` to one of --
-- `Γ'` of the same type at a grade entailed below, keeping the --
-- program context. It acts on derivations (`rename-v`,         --
-- `rename-c`) and on erasures as a renaming of positions. A    --
-- value of eternal type moves along any type-preserving map of --
-- positions (`eternal-v`). An extension `Ext Q Γ Γ' δ` makes   --
-- each variable older by at most `δ`.                          --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Typing.Renaming (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades              S
open import PolymorphicCalculus.Syntax.Types               S
open import PolymorphicCalculus.Syntax.Contexts            S
open import PolymorphicCalculus.Syntax.Contexts.Properties S
open import PolymorphicCalculus.Hypotheses                 S
open import PolymorphicCalculus.Typing                     S
open import PolymorphicCalculus.Typing.Erasure             S
open import PolymorphicCalculus.Syntax.Run                 S

------------------------------------------------------------------------
-- The run-time erasure of a derivation

∥_∥ᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ} → Q ∣ Γ ⊢ᵛ⦂ A → RunV n
∥ V ∥ᵛ = eraseᵛ ⌊ V ⌋ᵛ

∥_∥ᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ} → Q ∣ Γ ⊢ᶜ⦂ C → RunC n
∥ M ∥ᶜ = eraseᶜ ⌊ M ⌋ᶜ

∥res∥ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ' : RExp Θ} {A : OVType Θ}
      → (R : Q ⊢ A ∈̂[ ρ' ] Γ) → eraseᵛ ⌊ R ⌋ʳ ≡ var (var-pos (res-var-of R))
∥res∥ (res-var _)            = refl
∥res∥ (res-ann _ _ R _ _)    = ∥res∥ R

-- A resource value's annotations over another variable of its type

res-move : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m}
             {ρ' ρ'' : RExp Θ} {A : OVType Θ}
         → (R : Q ⊢ A ∈̂[ ρ' ] Γ)
         → [ res-grade-of R ] res-payload-of R ∈̂[ ρ'' ] Γ'
         → Q ⊢ A ∈̂[ ρ'' ] Γ'
res-move (res-var _)           z' = res-var z'
res-move (res-ann ρₐ Xₐ R p q) z' = res-ann ρₐ Xₐ (res-move R z') p q

∥res-move∥ : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m}
               {ρ' ρ'' : RExp Θ} {A : OVType Θ}
           → (R : Q ⊢ A ∈̂[ ρ' ] Γ)
           → (z' : [ res-grade-of R ] res-payload-of R ∈̂[ ρ'' ] Γ')
           → eraseᵛ ⌊ res-move R z' ⌋ʳ ≡ var (var-pos z')
∥res-move∥ (res-var _)         z' = refl
∥res-move∥ (res-ann _ _ R _ _) z' = ∥res-move∥ R z'

------------------------------------------------------------------------
-- Renamings

record Ren {Θ : Scope} {n m : ℕ} (Q : Hyps Θ) (Γ : OCtx Θ n) (Γ' : OCtx Θ m) : Set where
  field
    pos : Fin n → Fin m
    ty  : ∀ i → lookup-ty Γ' (pos i) ≡ lookup-ty Γ i
    gr  : ∀ i → Q ⊩ lookup-gr Γ' (pos i) ≾̂ᵣ lookup-gr Γ i
    dfs : defs Γ' ≡ defs Γ

open Ren public

-- The image of a variable

record Image {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m}
             (r : Ren Q Γ Γ') {A : OVType Θ} {ρ : RExp Θ} (x : A ∈̂[ ρ ] Γ) : Set where
  field
    grade  : RExp Θ
    mem    : A ∈̂[ grade ] Γ'
    lower  : Q ⊩ grade ≾̂ᵣ ρ
    at-pos : var-pos mem ≡ pos r (var-pos x)

open Image public

image : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {A ρ}
      → (r : Ren Q Γ Γ') → (x : A ∈̂[ ρ ] Γ) → Image r x
image {Q = Q} {Γ' = Γ'} r x = record
  { grade  = lookup-gr Γ' (pos r i)
  ; mem    = ∈̂-ty-subst eq (lookup-var Γ' (pos r i))
  ; lower  = subst (λ z → Q ⊩ lookup-gr Γ' (pos r i) ≾̂ᵣ z) (var-pos-gr x) (gr r i)
  ; at-pos = trans (var-pos-ty-subst eq _) (var-pos-lookup Γ' (pos r i))
  }
  where
    i  = var-pos x
    eq = trans (ty r i) (var-pos-ty x)

-- Lifting under a variable, a modality and an effect-grade variable

_⇑ʳ : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {A : OVType Θ}
    → Ren Q Γ Γ' → Ren Q (Γ ∷ A) (Γ' ∷ A)
pos (r ⇑ʳ) = ext (pos r)
ty  (r ⇑ʳ) zero    = refl
ty  (r ⇑ʳ) (suc i) = ty r i
gr  (r ⇑ʳ) zero    = ⊩≾̂ᵣ-refl
gr  (r ⇑ʳ) (suc i) = gr r i
dfs (r ⇑ʳ)         = dfs r

⟨⟩ʳ : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m}
    → (ρ : RExp Θ) → Ren Q Γ Γ' → Ren Q (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ ⟩)
pos (⟨⟩ʳ ρ r)   = pos r
ty  (⟨⟩ʳ ρ r)   = ty r
gr  (⟨⟩ʳ ρ r) i = monoᵣ (gr r i) ⊩≾̂ᵣ-refl
dfs (⟨⟩ʳ ρ r)   = dfs r

wkᵉʳ : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m}
     → Ren Q Γ Γ' → Ren (wkᵉ-H Q) (wkᵉ-ctx Γ) (wkᵉ-ctx Γ')
pos (wkᵉʳ r) = pos r
ty  (wkᵉʳ {Γ = Γ} {Γ'} r) i =
  trans (lookup-ty-wkᵉ Γ' (pos r i)) (trans (cong wkᵉ-v (ty r i)) (sym (lookup-ty-wkᵉ Γ i)))
gr  (wkᵉʳ {Q = Q} {Γ} {Γ'} r) i =
  subst₂ (λ x y → wkᵉ-H Q ⊩ x ≾̂ᵣ y)
         (sym (lookup-gr-wkᵉ Γ' (pos r i))) (sym (lookup-gr-wkᵉ Γ i))
         (⊩-wkᵉᵣ (gr r i))
dfs (wkᵉʳ {Γ = Γ} {Γ'} r) = trans (defs-wkᵉ Γ') (trans (dfs r) (sym (defs-wkᵉ Γ)))

clauseʳ : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {A B : OVType (Θ +e)}
        → Ren Q Γ Γ'
        → Ren (wkᵉ-H Q) (wkᵉ-ctx Γ ⟨ rconst ⊤ᵣ ⟩ ∷ A ∷ B) (wkᵉ-ctx Γ' ⟨ rconst ⊤ᵣ ⟩ ∷ A ∷ B)
clauseʳ r = (⟨⟩ʳ (rconst ⊤ᵣ) (wkᵉʳ r) ⇑ʳ) ⇑ʳ

------------------------------------------------------------------------
-- The action on derivations

mutual

  rename-v : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {A : OVType Θ}
           → Ren Q Γ Γ' → Q ∣ Γ ⊢ᵛ⦂ A → Q ∣ Γ' ⊢ᵛ⦂ A
  rename-v r (var x p)       =
    var (mem (image r x)) (Et∨≾ᵘ-≡̂ (≡̂ᵛ-refl _) (lower (image r x)) p)
  rename-v r (usedef f δ h e) = usedef (subst (_ ∈ᵖ[ _ ]_) (sym (dfs r)) f) δ h e
  rename-v r (const B c)     = const B c
  rename-v r ⋆               = ⋆
  rename-v r true            = true
  rename-v r false           = false
  rename-v r zero            = zero
  rename-v r (succ V)        = succ (rename-v r V)
  rename-v r ⦉ V , W ⦊        = ⦉ rename-v r V , rename-v r W ⦊
  rename-v r (inl V)         = inl (rename-v r V)
  rename-v r (inr V)         = inr (rename-v r V)
  rename-v r nil             = nil
  rename-v r (cons V W)      = cons (rename-v r V) (rename-v r W)
  rename-v r (cmp ⋈ V W et)  = cmp ⋈ (rename-v r V) (rename-v r W) et
  rename-v r (fun M)         = fun (rename-c (r ⇑ʳ) M)
  rename-v r (handler {ε = ε} N H) =
    handler (rename-c (⟨⟩ʳ ∣ ε ∣̂ᵉ r ⇑ʳ) N) (λ op → rename-c (clauseʳ r) (H op))
  rename-v r (annᵛ A V)      = annᵛ A (rename-v r V)
  rename-v r (subV V p)      = subV (rename-v r V) p

  rename-c : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {C : OCType Θ}
           → Ren Q Γ Γ' → Q ∣ Γ ⊢ᶜ⦂ C → Q ∣ Γ' ⊢ᶜ⦂ C
  rename-c r (return V)                 = return (rename-v r V)
  rename-c r (_⨟_ {ε = ε} M N)          = rename-c r M ⨟ rename-c (⟨⟩ʳ ∣ ε ∣̂ᵉ r ⇑ʳ) N
  rename-c r (V · W)                    = rename-v r V · rename-v r W
  rename-c r (match V `with M)          = match rename-v r V `with rename-c ((r ⇑ʳ) ⇑ʳ) M
  rename-c r (absurd V)                 = absurd (rename-v r V)
  rename-c r (if V `then M `else N)     =
    if rename-v r V `then rename-c r M `else rename-c r N
  rename-c r (matchℕ V `zero M `succ N) =
    matchℕ rename-v r V `zero rename-c r M `succ rename-c (r ⇑ʳ) N
  rename-c r (match+ V `inl M `inr N)   =
    match+ rename-v r V `inl rename-c (r ⇑ʳ) M `inr rename-c (r ⇑ʳ) N
  rename-c r (matchL V `nil M `cons N)  =
    matchL rename-v r V `nil rename-c r M `cons rename-c ((r ⇑ʳ) ⇑ʳ) N
  rename-c r (recℕ {ε = ε} V M N p)     =
    recℕ (rename-v r V) (rename-c r M)
         (rename-c (⟨⟩ʳ ∣ ε ∣̂ᵉ (⟨⟩ʳ (rconst ⊤ᵣ) r ⇑ʳ) ⇑ʳ) N) p
  rename-c r (recL {ε = ε} V M N p)     =
    recL (rename-v r V) (rename-c r M)
         (rename-c (⟨⟩ʳ ∣ ε ∣̂ᵉ ((⟨⟩ʳ (rconst ⊤ᵣ) r ⇑ʳ) ⇑ʳ) ⇑ʳ) N) p
  rename-c r (perform op V M)           =
    perform op (rename-v r V) (rename-c (⟨⟩ʳ (rconst ∣ op-grade op ∣ᵉ) r ⇑ʳ) M)
  rename-c r (delay τ M)                = delay τ (rename-c (⟨⟩ʳ (rconst (ιᵣ τ)) r) M)
  rename-c r (handle M `with V)         = handle rename-c r M `with rename-v r V
  rename-c r (unbox R p N)              =
    unbox (res-move R (mem (image r (res-var-of R)))) (transᵣ (lower (image r (res-var-of R))) p)
          (rename-c (r ⇑ʳ) N)
  rename-c r (box ρ V N)                = box ρ (rename-v (⟨⟩ʳ ρ r) V) (rename-c (r ⇑ʳ) N)
  rename-c r (annᶜ C M)                 = annᶜ C (rename-c r M)
  rename-c r (subC M p)                 = subC (rename-c r M) p

-- The erasure of a renamed derivation is the renamed erasure

mutual

  ∥rename-v∥ : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {A : OVType Θ}
             → (r : Ren Q Γ Γ') → (V : Q ∣ Γ ⊢ᵛ⦂ A) → ∥ rename-v r V ∥ᵛ ≡ renᵛ (pos r) ∥ V ∥ᵛ
  ∥rename-v∥ r (var x p)       = cong var (at-pos (image r x))
  ∥rename-v∥ r (usedef f δ h e) = refl
  ∥rename-v∥ r (const B c)     = refl
  ∥rename-v∥ r ⋆               = refl
  ∥rename-v∥ r true            = refl
  ∥rename-v∥ r false           = refl
  ∥rename-v∥ r zero            = refl
  ∥rename-v∥ r (succ V)        = cong succ (∥rename-v∥ r V)
  ∥rename-v∥ r ⦉ V , W ⦊        = cong₂ ⦉_,_⦊ (∥rename-v∥ r V) (∥rename-v∥ r W)
  ∥rename-v∥ r (inl V)         = cong inl (∥rename-v∥ r V)
  ∥rename-v∥ r (inr V)         = cong inr (∥rename-v∥ r V)
  ∥rename-v∥ r nil             = refl
  ∥rename-v∥ r (cons V W)      = cong₂ cons (∥rename-v∥ r V) (∥rename-v∥ r W)
  ∥rename-v∥ r (cmp ⋈ V W et)  = cong₂ (cmp ⋈) (∥rename-v∥ r V) (∥rename-v∥ r W)
  ∥rename-v∥ r (fun M)         = cong fun (∥rename-c∥ (r ⇑ʳ) M)
  ∥rename-v∥ r (handler {ε = ε} N H) =
    cong₂ handler (∥rename-c∥ (⟨⟩ʳ ∣ ε ∣̂ᵉ r ⇑ʳ) N)
                  (fun-ext (λ op → ∥rename-c∥ (clauseʳ r) (H op)))
  ∥rename-v∥ r (annᵛ A V)      = ∥rename-v∥ r V
  ∥rename-v∥ r (subV V p)      = ∥rename-v∥ r V

  ∥rename-c∥ : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {C : OCType Θ}
             → (r : Ren Q Γ Γ') → (M : Q ∣ Γ ⊢ᶜ⦂ C) → ∥ rename-c r M ∥ᶜ ≡ renᶜ (pos r) ∥ M ∥ᶜ
  ∥rename-c∥ r (return V)                 = cong return (∥rename-v∥ r V)
  ∥rename-c∥ r (_⨟_ {ε = ε} M N)          =
    cong₂ _⨟_ (∥rename-c∥ r M) (∥rename-c∥ (⟨⟩ʳ ∣ ε ∣̂ᵉ r ⇑ʳ) N)
  ∥rename-c∥ r (V · W)                    = cong₂ _·_ (∥rename-v∥ r V) (∥rename-v∥ r W)
  ∥rename-c∥ r (match V `with M)          =
    cong₂ match_`with_ (∥rename-v∥ r V) (∥rename-c∥ ((r ⇑ʳ) ⇑ʳ) M)
  ∥rename-c∥ r (absurd V)                 = cong absurd (∥rename-v∥ r V)
  ∥rename-c∥ r (if V `then M `else N)     =
    cong₃ if_`then_`else_ (∥rename-v∥ r V) (∥rename-c∥ r M) (∥rename-c∥ r N)
  ∥rename-c∥ r (matchℕ V `zero M `succ N) =
    cong₃ matchℕ_`zero_`succ_ (∥rename-v∥ r V) (∥rename-c∥ r M) (∥rename-c∥ (r ⇑ʳ) N)
  ∥rename-c∥ r (match+ V `inl M `inr N)   =
    cong₃ match+_`inl_`inr_ (∥rename-v∥ r V) (∥rename-c∥ (r ⇑ʳ) M) (∥rename-c∥ (r ⇑ʳ) N)
  ∥rename-c∥ r (matchL V `nil M `cons N)  =
    cong₃ matchL_`nil_`cons_ (∥rename-v∥ r V) (∥rename-c∥ r M) (∥rename-c∥ ((r ⇑ʳ) ⇑ʳ) N)
  ∥rename-c∥ r (recℕ {ε = ε} V M N p)     =
    cong₃ recℕ (∥rename-v∥ r V) (∥rename-c∥ r M)
               (∥rename-c∥ (⟨⟩ʳ ∣ ε ∣̂ᵉ (⟨⟩ʳ (rconst ⊤ᵣ) r ⇑ʳ) ⇑ʳ) N)
  ∥rename-c∥ r (recL {ε = ε} V M N p)     =
    cong₃ recL (∥rename-v∥ r V) (∥rename-c∥ r M)
               (∥rename-c∥ (⟨⟩ʳ ∣ ε ∣̂ᵉ ((⟨⟩ʳ (rconst ⊤ᵣ) r ⇑ʳ) ⇑ʳ) ⇑ʳ) N)
  ∥rename-c∥ r (perform op V M)           =
    cong₂ (perform op) (∥rename-v∥ r V)
                       (∥rename-c∥ (⟨⟩ʳ (rconst ∣ op-grade op ∣ᵉ) r ⇑ʳ) M)
  ∥rename-c∥ r (delay τ M)                =
    cong (delay τ) (∥rename-c∥ (⟨⟩ʳ (rconst (ιᵣ τ)) r) M)
  ∥rename-c∥ r (handle M `with V)         =
    cong₂ handle_`with_ (∥rename-c∥ r M) (∥rename-v∥ r V)
  ∥rename-c∥ r (unbox R p N)              =
    cong₂ unbox (trans (∥res-move∥ R (mem (image r (res-var-of R))))
                       (trans (cong var (at-pos (image r (res-var-of R))))
                              (cong (renᵛ (pos r)) (sym (∥res∥ R)))))
                (∥rename-c∥ (r ⇑ʳ) N)
  ∥rename-c∥ r (box ρ V N)                =
    cong₂ box (∥rename-v∥ (⟨⟩ʳ ρ r) V) (∥rename-c∥ (r ⇑ʳ) N)
  ∥rename-c∥ r (annᶜ C M)                 = ∥rename-c∥ r M
  ∥rename-c∥ r (subC M p)                 = ∥rename-c∥ r M

------------------------------------------------------------------------
-- Basic renamings

id-ren : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → Ren Q Γ Γ
pos id-ren i = i
ty  id-ren i = refl
gr  id-ren i = ⊩≾̂ᵣ-refl
dfs id-ren   = refl

_∘ʳ_ : ∀ {Θ n m k} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {Γ'' : OCtx Θ k}
     → Ren Q Γ' Γ'' → Ren Q Γ Γ' → Ren Q Γ Γ''
pos (s ∘ʳ r) i = pos s (pos r i)
ty  (s ∘ʳ r) i = trans (ty s (pos r i)) (ty r i)
gr  (s ∘ʳ r) i = transᵣ (gr s (pos r i)) (gr r i)
dfs (s ∘ʳ r)   = trans (dfs s) (dfs r)

wk-ren : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ} → Ren Q Γ (Γ ∷ A)
pos wk-ren = suc
ty  wk-ren i = refl
gr  wk-ren i = ⊩≾̂ᵣ-refl
dfs wk-ren   = refl

-- A modality above the unit may be removed; one below it inserted

⟨⟩-remove : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ : RExp Θ}
          → Q ⊩ 𝟏̂ᵣ ≾̂ᵣ ρ → Ren Q (Γ ⟨ ρ ⟩) Γ
pos (⟨⟩-remove le) i = i
ty  (⟨⟩-remove le) i = refl
gr  (⟨⟩-remove le) i = transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityʳ)) (monoᵣ ⊩≾̂ᵣ-refl le)
dfs (⟨⟩-remove le)   = refl

⟨⟩-insert : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ : RExp Θ}
          → Q ⊩ ρ ≾̂ᵣ 𝟏̂ᵣ → Ren Q Γ (Γ ⟨ ρ ⟩)
pos (⟨⟩-insert le) i = i
ty  (⟨⟩-insert le) i = refl
gr  (⟨⟩-insert le) i = transᵣ (monoᵣ ⊩≾̂ᵣ-refl le) (eqᵣ ≡̂ᵣ-identityʳ)
dfs (⟨⟩-insert le)   = refl

-- A modality may be lowered; two adjacent modalities are their product

⟨⟩-lower : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ ρ' : RExp Θ}
         → Q ⊩ ρ' ≾̂ᵣ ρ → Ren Q (Γ ⟨ ρ ⟩) (Γ ⟨ ρ' ⟩)
pos (⟨⟩-lower le) i = i
ty  (⟨⟩-lower le) i = refl
gr  (⟨⟩-lower le) i = monoᵣ ⊩≾̂ᵣ-refl le
dfs (⟨⟩-lower le)   = refl

⟨⟩-merge : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ ρ' : RExp Θ}
         → Ren Q (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩) (Γ ⟨ ρ ·̂ᵣ ρ' ⟩)
pos ⟨⟩-merge i = i
ty  ⟨⟩-merge i = refl
gr  ⟨⟩-merge i = eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-assoc)
dfs ⟨⟩-merge   = refl

⟨⟩-split : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ ρ' : RExp Θ}
         → Ren Q (Γ ⟨ ρ ·̂ᵣ ρ' ⟩) (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩)
pos ⟨⟩-split i = i
ty  ⟨⟩-split i = refl
gr  ⟨⟩-split i = eqᵣ ≡̂ᵣ-assoc
dfs ⟨⟩-split   = refl

------------------------------------------------------------------------
-- Values of eternal type

-- A map of positions preserving the types

record Shift {Θ : Scope} {n m : ℕ} (Γ : OCtx Θ n) (Γ' : OCtx Θ m) : Set where
  field
    shift    : Fin n → Fin m
    shift-ty : ∀ i → lookup-ty Γ' (shift i) ≡ lookup-ty Γ i
    shift-dfs : defs Γ' ≡ defs Γ

open Shift public

ren-shift : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} → Ren Q Γ Γ' → Shift Γ Γ'
shift    (ren-shift r) = pos r
shift-ty (ren-shift r) = ty r
shift-dfs (ren-shift r) = dfs r

mutual

  eternal-v : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {A : OVType Θ}
            → Shift Γ Γ' → Q ⊩Et A → Q ∣ Γ ⊢ᵛ⦂ A → Q ∣ Γ' ⊢ᵛ⦂ A
  eternal-v {Γ' = Γ'} f e (var x p) =
    var (∈̂-ty-subst (trans (shift-ty f (var-pos x)) (var-pos-ty x))
                    (lookup-var Γ' (shift f (var-pos x))))
        (et-ok e)
  eternal-v f e (usedef g δ h q)         = usedef (subst (_ ∈ᵖ[ _ ]_) (sym (shift-dfs f)) g) δ h q
  eternal-v f e (const B c)              = const B c
  eternal-v f e ⋆                        = ⋆
  eternal-v f e true                     = true
  eternal-v f e false                    = false
  eternal-v f e zero                     = zero
  eternal-v f e (succ V)                 = succ (eternal-v f e V)
  eternal-v f (e₁ |×|ₑ e₂) ⦉ V , W ⦊      = ⦉ eternal-v f e₁ V , eternal-v f e₂ W ⦊
  eternal-v f (e₁ |+|ₑ e₂) (inl V)       = inl (eternal-v f e₁ V)
  eternal-v f (e₁ |+|ₑ e₂) (inr V)       = inr (eternal-v f e₂ V)
  eternal-v f e nil                      = nil
  eternal-v f (listₑ e) (cons V W)       = cons (eternal-v f e V) (eternal-v f (listₑ e) W)
  eternal-v f e (cmp ⋈ V W et)           = cmp ⋈ (eternal-v f et V) (eternal-v f et W) et
  eternal-v f e (annᵛ A V)               = annᵛ A (eternal-v f e V)
  eternal-v f e (subV V p)               = subV (eternal-v f (<:̂ᵛ-eternalˡ p e) V) p

  ∥eternal-v∥ : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {A : OVType Θ}
              → (f : Shift Γ Γ') → (e : Q ⊩Et A) → (V : Q ∣ Γ ⊢ᵛ⦂ A)
              → ∥ eternal-v f e V ∥ᵛ ≡ renᵛ (shift f) ∥ V ∥ᵛ
  ∥eternal-v∥ {Γ' = Γ'} f e (var x p) =
    cong var (trans (var-pos-ty-subst (trans (shift-ty f (var-pos x)) (var-pos-ty x)) _)
                    (var-pos-lookup Γ' (shift f (var-pos x))))
  ∥eternal-v∥ f e (usedef g δ h q)     = refl
  ∥eternal-v∥ f e (const B c)          = refl
  ∥eternal-v∥ f e ⋆                    = refl
  ∥eternal-v∥ f e true                 = refl
  ∥eternal-v∥ f e false                = refl
  ∥eternal-v∥ f e zero                 = refl
  ∥eternal-v∥ f e (succ V)             = cong succ (∥eternal-v∥ f e V)
  ∥eternal-v∥ f (e₁ |×|ₑ e₂) ⦉ V , W ⦊  = cong₂ ⦉_,_⦊ (∥eternal-v∥ f e₁ V) (∥eternal-v∥ f e₂ W)
  ∥eternal-v∥ f (e₁ |+|ₑ e₂) (inl V)   = cong inl (∥eternal-v∥ f e₁ V)
  ∥eternal-v∥ f (e₁ |+|ₑ e₂) (inr V)   = cong inr (∥eternal-v∥ f e₂ V)
  ∥eternal-v∥ f e nil                  = refl
  ∥eternal-v∥ f (listₑ e) (cons V W)   =
    cong₂ cons (∥eternal-v∥ f e V) (∥eternal-v∥ f (listₑ e) W)
  ∥eternal-v∥ f e (cmp ⋈ V W et)       = cong₂ (cmp ⋈) (∥eternal-v∥ f et V) (∥eternal-v∥ f et W)
  ∥eternal-v∥ f e (annᵛ A V)           = ∥eternal-v∥ f e V
  ∥eternal-v∥ f e (subV V p)           = ∥eternal-v∥ f (<:̂ᵛ-eternalˡ p e) V

------------------------------------------------------------------------
-- Extensions: a renaming whose images are older by at most `δ`

record Ext {Θ : Scope} {n m : ℕ} (Q : Hyps Θ) (Γ : OCtx Θ n) (Γ' : OCtx Θ m)
           (δ : RExp Θ) : Set where
  field
    epos : Fin n → Fin m
    ety  : ∀ i → lookup-ty Γ' (epos i) ≡ lookup-ty Γ i
    egr  : ∀ i → Q ⊩ lookup-gr Γ' (epos i) ≾̂ᵣ lookup-gr Γ i ·̂ᵣ δ
    edfs : defs Γ' ≡ defs Γ

open Ext public

-- The renamings an extension gives behind and in place of modalities

ext-⟨⟩ : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {δ ρ ρ' : RExp Θ}
       → Ext Q Γ Γ' δ → Q ⊩ δ ·̂ᵣ ρ' ≾̂ᵣ ρ → Ren Q (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ' ⟩)
pos (ext-⟨⟩ e le)   = epos e
ty  (ext-⟨⟩ e le)   = ety e
gr  (ext-⟨⟩ e le) i =
  transᵣ (monoᵣ (egr e i) ⊩≾̂ᵣ-refl) (transᵣ (eqᵣ ≡̂ᵣ-assoc) (monoᵣ ⊩≾̂ᵣ-refl le))
dfs (ext-⟨⟩ e le) = edfs e

ext-⟨⟩-remove : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {δ ρ : RExp Θ}
              → Ext Q Γ Γ' δ → Q ⊩ δ ≾̂ᵣ ρ → Ren Q (Γ ⟨ ρ ⟩) Γ'
pos (ext-⟨⟩-remove e le) = epos e
ty  (ext-⟨⟩-remove e le) = ety e
gr  (ext-⟨⟩-remove e le) i = transᵣ (egr e i) (monoᵣ ⊩≾̂ᵣ-refl le)
dfs (ext-⟨⟩-remove e le)   = edfs e

ext-top : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {δ : RExp Θ}
        → Ext Q Γ Γ' δ → Ren Q (Γ ⟨ rconst ⊤ᵣ ⟩) (Γ' ⟨ rconst ⊤ᵣ ⟩)
ext-top e = ext-⟨⟩ e topᵣ

ext-clause : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {δ : RExp Θ}
               {A B : OVType (Θ +e)}
           → Ext Q Γ Γ' δ
           → Ren (wkᵉ-H Q) (wkᵉ-ctx Γ ⟨ rconst ⊤ᵣ ⟩ ∷ A ∷ B) (wkᵉ-ctx Γ' ⟨ rconst ⊤ᵣ ⟩ ∷ A ∷ B)
ext-clause e = (wkᵉʳ (ext-top e) ⇑ʳ) ⇑ʳ

ext-∘ʳ : ∀ {Θ n m k} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {Γ'' : OCtx Θ k} {δ : RExp Θ}
       → Ext Q Γ' Γ'' δ → Ren Q Γ Γ' → Ext Q Γ Γ'' δ
epos (ext-∘ʳ e r) i = epos e (pos r i)
ety  (ext-∘ʳ e r) i = trans (ety e (pos r i)) (ty r i)
egr  (ext-∘ʳ e r) i = transᵣ (egr e (pos r i)) (monoᵣ (gr r i) ⊩≾̂ᵣ-refl)
edfs (ext-∘ʳ e r)   = trans (edfs e) (dfs r)

id-ext : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} → Ext Q Γ Γ 𝟏̂ᵣ
epos id-ext i = i
ety  id-ext i = refl
egr  id-ext i = eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityʳ)
edfs id-ext   = refl

⟨⟩-ext : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ : RExp Θ} → Ext Q Γ (Γ ⟨ ρ ⟩) ρ
epos ⟨⟩-ext i = i
ety  ⟨⟩-ext i = refl
egr  ⟨⟩-ext i = ⊩≾̂ᵣ-refl
edfs ⟨⟩-ext   = refl

wk-ext : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {δ : RExp Θ} {A : OVType Θ}
       → Ext Q Γ Γ' δ → Ext Q Γ (Γ' ∷ A) δ
epos (wk-ext e) i = suc (epos e i)
ety  (wk-ext e) i = ety e i
egr  (wk-ext e) i = egr e i
edfs (wk-ext e)   = edfs e
