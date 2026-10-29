------------------------------------------------------------------
-- Substitution of a value for a term variable                  --
--                                                              --
-- Under the truths: a variable `x : A` at depth               --
-- `k` of `Γ` (`Drop Γ₀ A k Γ Γ⁻`, with `Γ₀` the context before --
-- `x` and `Γ⁻` the context without it), and a value of type    --
-- `A` in `Γ₀`, give `Γ⁻ ⊢ M[V/x]` from `Γ ⊢ M` (`sub-v`,       --
-- `sub-c`), erasing to the run-time substitution `subᶜ k`.     --
--                                                              --
-- A use of `x` behind locks of grade `ρ` meets `x`'s side      --
-- condition: `A` is eternal, and `V` moves past the locks as   --
-- an eternal value, or `ρ` is below the unit, and `V` moves    --
-- past them by a renaming. An `unbox` of `x` unboxes the       --
-- variable that `V`, a value of box type, is.                  --
------------------------------------------------------------------

open import Data.Fin using (zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ-syntax; _,_)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Typing.Substitution (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OpenCalculus.Syntax.Grades         S
open import OpenCalculus.Syntax.Types          S
open import OpenCalculus.Syntax.Contexts       S
open import OpenCalculus.Syntax.ContextsLemmas S
open import OpenCalculus.Syntax.Subst          S
open import OpenCalculus.Hypotheses            S
open import OpenCalculus.Typing                S
open import OpenCalculus.Typing.Erasure        S
open import OpenCalculus.Typing.Transport      S
open import OpenCalculus.Typing.GradeSubstitution S
open import OpenCalculus.Typing.Renaming       S
open import OpenCalculus.Syntax.Run            S

------------------------------------------------------------------------
-- Dropping the variable at depth `k`

data Drop {Θ : Scope} {n : ℕ} (Γ₀ : OCtx Θ n) (A : OVType Θ)
     : (k : ℕ) → OCtx Θ (k + suc n) → OCtx Θ (k + n) → Set where
  here    : Drop Γ₀ A 0 (Γ₀ ∷ A) Γ₀
  there∷  : ∀ {k Γ Γ⁻ B} → Drop Γ₀ A k Γ Γ⁻ → Drop Γ₀ A (suc k) (Γ ∷ B) (Γ⁻ ∷ B)
  there⟨⟩ : ∀ {k Γ Γ⁻ ρ} → Drop Γ₀ A k Γ Γ⁻ → Drop Γ₀ A k (Γ ⟨ ρ ⟩) (Γ⁻ ⟨ ρ ⟩)

module _ {Θ : Scope} {n : ℕ} {Γ₀ : OCtx Θ n} {A : OVType Θ} where

  -- the grade accumulated at the dropped variable

  dgrade : ∀ {k Γ Γ⁻} → Drop Γ₀ A k Γ Γ⁻ → RExp Θ
  dgrade here                    = ûᵣ
  dgrade (there∷ d)              = dgrade d
  dgrade (there⟨⟩ {ρ = ρ} d)     = dgrade d ·̂ᵣ ρ

  -- the variables before the dropped one, in the context without it

  dshift : ∀ {k Γ Γ⁻} → Drop Γ₀ A k Γ Γ⁻ → Shift Γ₀ Γ⁻
  shift    (dshift here)        i = i
  shift-ty (dshift here)        i = refl
  shift    (dshift (there∷ d))  i = suc (shift (dshift d) i)
  shift-ty (dshift (there∷ d))  i = shift-ty (dshift d) i
  shift    (dshift (there⟨⟩ d)) i = shift (dshift d) i
  shift-ty (dshift (there⟨⟩ d)) i = shift-ty (dshift d) i

  dshift-gr : ∀ {k Γ Γ⁻} {Q : Hyps Θ} → (d : Drop Γ₀ A k Γ Γ⁻) → ∀ i
            → Q ⊩ lookup-gr Γ⁻ (shift (dshift d) i) ≾̂ᵣ lookup-gr Γ₀ i ·̂ᵣ dgrade d
  dshift-gr here        i = eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityʳ)
  dshift-gr (there∷ d)  i = dshift-gr d i
  dshift-gr (there⟨⟩ d) i = transᵣ (monoᵣ (dshift-gr d i) ⊩≾̂ᵣ-refl) (eqᵣ ≡̂ᵣ-assoc)

  -- below the unit, a renaming

  drop-ren : ∀ {k Γ Γ⁻} {Q : Hyps Θ} → (d : Drop Γ₀ A k Γ Γ⁻) → Q ⊩ dgrade d ≾̂ᵣ ûᵣ
           → Ren Q Γ₀ Γ⁻
  pos (drop-ren d le) = shift (dshift d)
  ty  (drop-ren d le) = shift-ty (dshift d)
  gr  (drop-ren d le) i =
    transᵣ (dshift-gr d i) (transᵣ (monoᵣ ⊩≾̂ᵣ-refl le) (eqᵣ ≡̂ᵣ-identityʳ))

  -- A variable of the context is the dropped one or one of the context
  -- without it

  data DropView {k Γ Γ⁻} (d : Drop Γ₀ A k Γ Γ⁻) {B : OVType Θ} {ρ : RExp Θ}
       (x : B ∈̂[ ρ ] Γ) : Set where
    hit  : B ≡ A → ρ ≡ dgrade d
         → (∀ (U : RunV n) → subVar k U (var-pos x) ≡ renᵛ (shift (dshift d)) U)
         → DropView d x
    miss : (x' : B ∈̂[ ρ ] Γ⁻)
         → (∀ (U : RunV n) → subVar k U (var-pos x) ≡ var (var-pos x'))
         → DropView d x

  drop-view : ∀ {k Γ Γ⁻} {B ρ} → (d : Drop Γ₀ A k Γ Γ⁻) → (x : B ∈̂[ ρ ] Γ) → DropView d x
  drop-view here        Hd        = hit refl refl (λ U → sym (ren-idᵛ (λ i → refl) U))
  drop-view here        (Tl-∷ x)  = miss x (λ U → refl)
  drop-view (there∷ d)  Hd        = miss Hd (λ U → refl)
  drop-view (there∷ d)  (Tl-∷ x)  with drop-view d x
  ... | hit eB eρ e  = hit eB eρ (λ U → trans (cong wkᵛ (e U)) (ren-fuseᵛ (λ i → refl) U))
  ... | miss x' e    = miss (Tl-∷ x') (λ U → cong wkᵛ (e U))
  drop-view (there⟨⟩ {ρ = ρ} d) (Tl-⟨⟩ x) with drop-view d x
  ... | hit eB eρ e  = hit eB (cong (_·̂ᵣ ρ) eρ) e
  ... | miss x' e    = miss (Tl-⟨⟩ x') e

-- Lifting a dropped variable over an effect-grade variable

wkᵉ-drop : ∀ {Θ n k} {Γ₀ : OCtx Θ n} {A : OVType Θ} {Γ Γ⁻}
         → Drop Γ₀ A k Γ Γ⁻ → Drop (wkᵉ-ctx Γ₀) (wkᵉ-v A) k (wkᵉ-ctx Γ) (wkᵉ-ctx Γ⁻)
wkᵉ-drop here        = here
wkᵉ-drop (there∷ d)  = there∷ (wkᵉ-drop d)
wkᵉ-drop (there⟨⟩ d) = there⟨⟩ (wkᵉ-drop d)

-- a value weakened by an effect-grade variable

wkᵉ-val : ∀ {Θ n} {Γ : OCtx Θ n} {A : OVType Θ}
        → ⊤ᴴ ∣ Γ ⊢V⦂ A → ⊤ᴴ ∣ wkᵉ-ctx Γ ⊢V⦂ wkᵉ-v A
wkᵉ-val {Γ = Γ} {A} V = ty-subst (wkˢᵉ-v A) (ctx-castᵛ (wkˢᵉ-ctx Γ) (substᵛ wkˢᵉ ⊩ᴴ-wkᵉ V))

∥wkᵉ-val∥ : ∀ {Θ n} {Γ : OCtx Θ n} {A : OVType Θ}
          → (V : ⊤ᴴ ∣ Γ ⊢V⦂ A) → ∥ wkᵉ-val V ∥ᵛ ≡ ∥ V ∥ᵛ
∥wkᵉ-val∥ {Γ = Γ} {A} V =
  trans (cong eraseᵛ (trans (⌊ty-subst⌋ (wkˢᵉ-v A) _)
                            (trans (⌊ctx-castᵛ⌋ (wkˢᵉ-ctx Γ) _) (⌊substᵛ⌋ wkˢᵉ ⊩ᴴ-wkᵉ V))))
        (erase-substᵛ ⌊ V ⌋ᵛ wkˢᵉ)

------------------------------------------------------------------------
-- A value of box type is a variable, under subsumptions

record BoxVar {Θ n} (Γ : OCtx Θ n) (ρ₀ : RExp Θ) (A₀ : OVType Θ) (U : RunV n) : Set where
  field
    cell-grade : RExp Θ
    cell-type  : OVType Θ
    age        : RExp Θ
    cell       : [ cell-grade ] cell-type ∈̂[ age ] Γ
    young      : ⊤ᴴ ⊩ age ≾̂ᵣ ûᵣ
    wider      : ⊤ᴴ ⊩ ρ₀ ≾̂ᵣ cell-grade
    narrower   : ⊤ᴴ ∣ cell-type <:̂ᵛ A₀
    is-cell    : U ≡ var (var-pos cell)

open BoxVar public

box-var : ∀ {Θ n} {Γ : OCtx Θ n} {ρ₀ : RExp Θ} {A₀ : OVType Θ}
        → (V : ⊤ᴴ ∣ Γ ⊢V⦂ [ ρ₀ ] A₀) → BoxVar Γ ρ₀ A₀ ∥ V ∥ᵛ
box-var (var x (≾ᵘ-ok le)) =
  record { cell = x ; young = le ; wider = ⊩≾̂ᵣ-refl ; narrower = <:̂ᵛ-refl _ ; is-cell = refl }
box-var (var x (hyp-ok () _ _))
box-var (annᵛ _ V) = box-var V
box-var (subV V ([ p ]ₛ q)) =
  record { cell = cell b ; young = young b ; wider = transᵣ p (wider b)
         ; narrower = <:̂ᵛ-trans (narrower b) q ; is-cell = is-cell b }
  where b = box-var V

------------------------------------------------------------------------
-- The substitution lemma

-- The dropped variable, used behind locks of the grade it accumulates

sub-var : ∀ {Θ n k} {Γ₀ : OCtx Θ n} {A : OVType Θ} {Γ Γ⁻} {B ρ}
        → (d : Drop Γ₀ A k Γ Γ⁻) → ⊤ᴴ ∣ Γ₀ ⊢V⦂ A
        → (x : B ∈̂[ ρ ] Γ) → VarOK ⊤ᴴ B ρ → DropView d x
        → ⊤ᴴ ∣ Γ⁻ ⊢V⦂ B
sub-var d U x p              (miss x' _)       = var x' p
sub-var d U x (et-ok e)      (hit refl refl _) = eternal-v (dshift d) e U
sub-var d U x (≾ᵘ-ok le)     (hit refl refl _) = rename-v (drop-ren d le) U
sub-var d U x (hyp-ok () _ _) (hit refl refl _)

∥sub-var∥ : ∀ {Θ n k} {Γ₀ : OCtx Θ n} {A : OVType Θ} {Γ Γ⁻} {B ρ}
          → (d : Drop Γ₀ A k Γ Γ⁻) → (U : ⊤ᴴ ∣ Γ₀ ⊢V⦂ A)
          → (x : B ∈̂[ ρ ] Γ) → (p : VarOK ⊤ᴴ B ρ) → (v : DropView d x)
          → ∥ sub-var d U x p v ∥ᵛ ≡ subVar k ∥ U ∥ᵛ (var-pos x)
∥sub-var∥ d U x p          (miss x' q)       = sym (q _)
∥sub-var∥ d U x (et-ok e)  (hit refl refl q) = trans (∥eternal-v∥ (dshift d) e U) (sym (q _))
∥sub-var∥ d U x (≾ᵘ-ok le) (hit refl refl q) = trans (∥rename-v∥ (drop-ren d le) U) (sym (q _))
∥sub-var∥ d U x (hyp-ok () _ _) (hit refl refl q)

-- An `unbox` of the dropped variable unboxes the variable that the
-- substituted value is

sub-unbox : ∀ {Θ n k} {Γ₀ : OCtx Θ n} {A : OVType Θ} {Γ Γ⁻} {A' A₀ : OVType Θ}
              {C : OCType Θ} {ρ₀ ρ'}
          → (d : Drop Γ₀ A k Γ Γ⁻) → ⊤ᴴ ∣ Γ₀ ⊢V⦂ A
          → (x : [ ρ₀ ] A₀ ∈̂[ ρ' ] Γ) → ⊤ᴴ ⊩ ρ' ≾̂ᵣ ρ₀ → ⊤ᴴ ∣ A₀ <:̂ᵛ A'
          → ⊤ᴴ ∣ Γ⁻ ∷ A' ⊢C⦂ C → DropView d x
          → ⊤ᴴ ∣ Γ⁻ ⊢C⦂ C
sub-unbox {Γ⁻ = Γ⁻} d U x p q N (hit refl refl _) =
  unbox (∈̂-ty-subst eq (lookup-var Γ⁻ j))
        (transᵣ (dshift-gr d i)
          (transᵣ (monoᵣ (subst (λ z → ⊤ᴴ ⊩ z ≾̂ᵣ ûᵣ) (sym (var-pos-gr (cell b))) (young b))
                   ⊩≾̂ᵣ-refl)
            (transᵣ (eqᵣ ≡̂ᵣ-identityˡ) (transᵣ p (wider b)))))
        (<:̂ᵛ-trans (narrower b) q) N
  where
    b  = box-var U
    i  = var-pos (cell b)
    j  = shift (dshift d) i
    eq = trans (shift-ty (dshift d) i) (var-pos-ty (cell b))
sub-unbox d U x p q N (miss x' _) = unbox x' p q N

∥sub-unbox∥ : ∀ {Θ n k} {Γ₀ : OCtx Θ n} {A : OVType Θ} {Γ Γ⁻} {A' A₀ : OVType Θ}
                {C : OCType Θ} {ρ₀ ρ'}
            → (d : Drop Γ₀ A k Γ Γ⁻) → (U : ⊤ᴴ ∣ Γ₀ ⊢V⦂ A)
            → (x : [ ρ₀ ] A₀ ∈̂[ ρ' ] Γ) → (p : ⊤ᴴ ⊩ ρ' ≾̂ᵣ ρ₀) → (q : ⊤ᴴ ∣ A₀ <:̂ᵛ A')
            → (N : ⊤ᴴ ∣ Γ⁻ ∷ A' ⊢C⦂ C) → (v : DropView d x)
            → ∥ sub-unbox d U x p q N v ∥ᶜ ≡ unbox (subVar k ∥ U ∥ᵛ (var-pos x)) ∥ N ∥ᶜ
∥sub-unbox∥ {Γ⁻ = Γ⁻} d U x p q N (hit refl refl e) =
  cong (λ z → unbox z ∥ N ∥ᶜ)
       (trans (cong var (trans (var-pos-ty-subst eq _) (var-pos-lookup Γ⁻ j)))
              (sym (trans (e ∥ U ∥ᵛ) (cong (renᵛ (shift (dshift d))) (is-cell b)))))
  where
    b  = box-var U
    i  = var-pos (cell b)
    j  = shift (dshift d) i
    eq = trans (shift-ty (dshift d) i) (var-pos-ty (cell b))
∥sub-unbox∥ d U x p q N (miss x' e) = cong (λ z → unbox z ∥ N ∥ᶜ) (sym (e _))

mutual

  sub-v : ∀ {Θ n k} {Γ₀ : OCtx Θ n} {A : OVType Θ} {Γ Γ⁻} {B : OVType Θ}
        → Drop Γ₀ A k Γ Γ⁻ → ⊤ᴴ ∣ Γ₀ ⊢V⦂ A → ⊤ᴴ ∣ Γ ⊢V⦂ B → ⊤ᴴ ∣ Γ⁻ ⊢V⦂ B
  sub-v d U (var x p)      = sub-var d U x p (drop-view d x)
  sub-v d U (const B c)    = const B c
  sub-v d U ⋆              = ⋆
  sub-v d U true           = true
  sub-v d U false          = false
  sub-v d U zero           = zero
  sub-v d U (succ V)       = succ (sub-v d U V)
  sub-v d U ⦉ V , W ⦊       = ⦉ sub-v d U V , sub-v d U W ⦊
  sub-v d U (inl V)        = inl (sub-v d U V)
  sub-v d U (inr V)        = inr (sub-v d U V)
  sub-v d U nil            = nil
  sub-v d U (cons V W)     = cons (sub-v d U V) (sub-v d U W)
  sub-v d U (cmp ⋈ V W et) = cmp ⋈ (sub-v d U V) (sub-v d U W) et
  sub-v d U (lam M)        = lam (sub-c (there∷ d) U M)
  sub-v d U (handler N H)  =
    handler (sub-c (there∷ (there⟨⟩ d)) U N)
            (λ op → sub-c (there∷ (there∷ (there⟨⟩ (wkᵉ-drop d)))) (wkᵉ-val U) (H op))
  sub-v d U (annᵛ A V)     = annᵛ A (sub-v d U V)
  sub-v d U (subV V p)     = subV (sub-v d U V) p

  sub-c : ∀ {Θ n k} {Γ₀ : OCtx Θ n} {A : OVType Θ} {Γ Γ⁻} {C : OCType Θ}
        → Drop Γ₀ A k Γ Γ⁻ → ⊤ᴴ ∣ Γ₀ ⊢V⦂ A → ⊤ᴴ ∣ Γ ⊢C⦂ C → ⊤ᴴ ∣ Γ⁻ ⊢C⦂ C
  sub-c d U (return V)                = return (sub-v d U V)
  sub-c d U (M ⨟ N)                   = sub-c d U M ⨟ sub-c (there∷ (there⟨⟩ d)) U N
  sub-c d U (V · W)                   = sub-v d U V · sub-v d U W
  sub-c d U (match V `in M)           = match sub-v d U V `in sub-c (there∷ (there∷ d)) U M
  sub-c d U (absurd V)                = absurd (sub-v d U V)
  sub-c d U (if V `then M `else N)    = if sub-v d U V `then sub-c d U M `else sub-c d U N
  sub-c d U (caseℕ V `zero M `succ N) =
    caseℕ sub-v d U V `zero sub-c d U M `succ sub-c (there∷ d) U N
  sub-c d U (case+ V `inl M `inr N)   =
    case+ sub-v d U V `inl sub-c (there∷ d) U M `inr sub-c (there∷ d) U N
  sub-c d U (caseL V `nil M `cons N)  =
    caseL sub-v d U V `nil sub-c d U M `cons sub-c (there∷ (there∷ d)) U N
  sub-c d U (recℕ V M N p)            =
    recℕ (sub-v d U V) (sub-c d U M) (sub-c (there∷ (there⟨⟩ (there∷ (there⟨⟩ d)))) U N) p
  sub-c d U (recL V M N p)            =
    recL (sub-v d U V) (sub-c d U M)
         (sub-c (there∷ (there⟨⟩ (there∷ (there∷ (there⟨⟩ d))))) U N) p
  sub-c d U (perform op V M)          = perform op (sub-v d U V) (sub-c (there∷ (there⟨⟩ d)) U M)
  sub-c d U (delay τ M)               = delay τ (sub-c (there⟨⟩ d) U M)
  sub-c d U (handle M `with V)        = handle sub-c d U M `with sub-v d U V
  sub-c d U (unbox x p q N)           = sub-unbox d U x p q (sub-c (there∷ d) U N) (drop-view d x)
  sub-c d U (box ρ V N)               = box ρ (sub-v (there⟨⟩ d) U V) (sub-c (there∷ d) U N)
  sub-c d U (annᶜ C M)                = annᶜ C (sub-c d U M)
  sub-c d U (subC M p)                = subC (sub-c d U M) p

-- The erasure of the substituted derivation is the run-time substitution

mutual

  ∥sub-v∥ : ∀ {Θ n k} {Γ₀ : OCtx Θ n} {A : OVType Θ} {Γ Γ⁻} {B : OVType Θ}
          → (d : Drop Γ₀ A k Γ Γ⁻) → (U : ⊤ᴴ ∣ Γ₀ ⊢V⦂ A) → (V : ⊤ᴴ ∣ Γ ⊢V⦂ B)
          → ∥ sub-v d U V ∥ᵛ ≡ subᵛ k ∥ U ∥ᵛ ∥ V ∥ᵛ
  ∥sub-v∥ d U (var x p)      = ∥sub-var∥ d U x p (drop-view d x)
  ∥sub-v∥ d U (const B c)    = refl
  ∥sub-v∥ d U ⋆              = refl
  ∥sub-v∥ d U true           = refl
  ∥sub-v∥ d U false          = refl
  ∥sub-v∥ d U zero           = refl
  ∥sub-v∥ d U (succ V)       = cong succ (∥sub-v∥ d U V)
  ∥sub-v∥ d U ⦉ V , W ⦊       = cong₂ ⦉_,_⦊ (∥sub-v∥ d U V) (∥sub-v∥ d U W)
  ∥sub-v∥ d U (inl V)        = cong inl (∥sub-v∥ d U V)
  ∥sub-v∥ d U (inr V)        = cong inr (∥sub-v∥ d U V)
  ∥sub-v∥ d U nil            = refl
  ∥sub-v∥ d U (cons V W)     = cong₂ cons (∥sub-v∥ d U V) (∥sub-v∥ d U W)
  ∥sub-v∥ d U (cmp ⋈ V W et) = cong₂ (cmp ⋈) (∥sub-v∥ d U V) (∥sub-v∥ d U W)
  ∥sub-v∥ d U (lam M)        = cong lam (∥sub-c∥ (there∷ d) U M)
  ∥sub-v∥ d U (handler N H)  =
    cong₂ handler (∥sub-c∥ (there∷ (there⟨⟩ d)) U N)
          (fun-ext (λ op →
            trans (∥sub-c∥ (there∷ (there∷ (there⟨⟩ (wkᵉ-drop d)))) (wkᵉ-val U) (H op))
                  (cong (λ z → subᶜ _ z ∥ H op ∥ᶜ) (∥wkᵉ-val∥ U))))
  ∥sub-v∥ d U (annᵛ A V)     = ∥sub-v∥ d U V
  ∥sub-v∥ d U (subV V p)     = ∥sub-v∥ d U V

  ∥sub-c∥ : ∀ {Θ n k} {Γ₀ : OCtx Θ n} {A : OVType Θ} {Γ Γ⁻} {C : OCType Θ}
          → (d : Drop Γ₀ A k Γ Γ⁻) → (U : ⊤ᴴ ∣ Γ₀ ⊢V⦂ A) → (M : ⊤ᴴ ∣ Γ ⊢C⦂ C)
          → ∥ sub-c d U M ∥ᶜ ≡ subᶜ k ∥ U ∥ᵛ ∥ M ∥ᶜ
  ∥sub-c∥ d U (return V)                = cong return (∥sub-v∥ d U V)
  ∥sub-c∥ d U (M ⨟ N)                   =
    cong₂ _⨟_ (∥sub-c∥ d U M) (∥sub-c∥ (there∷ (there⟨⟩ d)) U N)
  ∥sub-c∥ d U (V · W)                   = cong₂ _·_ (∥sub-v∥ d U V) (∥sub-v∥ d U W)
  ∥sub-c∥ d U (match V `in M)           =
    cong₂ match_`in_ (∥sub-v∥ d U V) (∥sub-c∥ (there∷ (there∷ d)) U M)
  ∥sub-c∥ d U (absurd V)                = cong absurd (∥sub-v∥ d U V)
  ∥sub-c∥ d U (if V `then M `else N)    =
    cong₃ if_`then_`else_ (∥sub-v∥ d U V) (∥sub-c∥ d U M) (∥sub-c∥ d U N)
  ∥sub-c∥ d U (caseℕ V `zero M `succ N) =
    cong₃ caseℕ_`zero_`succ_ (∥sub-v∥ d U V) (∥sub-c∥ d U M) (∥sub-c∥ (there∷ d) U N)
  ∥sub-c∥ d U (case+ V `inl M `inr N)   =
    cong₃ case+_`inl_`inr_ (∥sub-v∥ d U V) (∥sub-c∥ (there∷ d) U M) (∥sub-c∥ (there∷ d) U N)
  ∥sub-c∥ d U (caseL V `nil M `cons N)  =
    cong₃ caseL_`nil_`cons_ (∥sub-v∥ d U V) (∥sub-c∥ d U M) (∥sub-c∥ (there∷ (there∷ d)) U N)
  ∥sub-c∥ d U (recℕ V M N p)            =
    cong₃ recℕ (∥sub-v∥ d U V) (∥sub-c∥ d U M)
               (∥sub-c∥ (there∷ (there⟨⟩ (there∷ (there⟨⟩ d)))) U N)
  ∥sub-c∥ d U (recL V M N p)            =
    cong₃ recL (∥sub-v∥ d U V) (∥sub-c∥ d U M)
               (∥sub-c∥ (there∷ (there⟨⟩ (there∷ (there∷ (there⟨⟩ d))))) U N)
  ∥sub-c∥ d U (perform op V M)          =
    cong₂ (perform op) (∥sub-v∥ d U V) (∥sub-c∥ (there∷ (there⟨⟩ d)) U M)
  ∥sub-c∥ d U (delay τ M)               = cong (delay τ) (∥sub-c∥ (there⟨⟩ d) U M)
  ∥sub-c∥ d U (handle M `with V)        =
    cong₂ handle_`with_ (∥sub-c∥ d U M) (∥sub-v∥ d U V)
  ∥sub-c∥ d U (unbox x p q N)           =
    trans (∥sub-unbox∥ d U x p q (sub-c (there∷ d) U N) (drop-view d x))
          (cong (unbox _) (∥sub-c∥ (there∷ d) U N))
  ∥sub-c∥ d U (box ρ V N)               =
    cong₂ box (∥sub-v∥ (there⟨⟩ d) U V) (∥sub-c∥ (there∷ d) U N)
  ∥sub-c∥ d U (annᶜ C M)                = ∥sub-c∥ d U M
  ∥sub-c∥ d U (subC M p)                = ∥sub-c∥ d U M
