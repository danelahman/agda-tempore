------------------------------------------------------------------
-- Conversion of the types of a context                         --
--                                                              --
-- A conversion relates a type `A'` that may replace a context  --
-- type `A`: `A'` is a subtype of `A`, meets the side condition --
-- of `var` wherever `A` does, under admissible hypotheses, and --
-- relates the payloads of box types. Contexts related          --
-- pointwise (`CtxRel`) type the same terms, with the same      --
-- erasure (`conv-v`, `conv-c`): a variable is used at its new  --
-- type under a `subV`, and an `unbox` of a variable whose      --
-- type changes binds the new payload when the resource value   --
-- has no annotation.                                           --
--                                                              --
-- Two conversions: equivalence, mutual subtyping, under any    --
-- hypotheses (`equivalence`); and narrowing, subtyping, under  --
-- hypotheses with no `disj` hypothesis (`narrowing`).          --
------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Fin using (suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Typing.Conversion (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OpenCalculus.Syntax.Grades         S
open import OpenCalculus.Syntax.Types          S
open import OpenCalculus.Syntax.Contexts       S
open import OpenCalculus.Syntax.ContextsLemmas S
open import OpenCalculus.Hypotheses            S
open import OpenCalculus.Typing                S
open import OpenCalculus.Typing.Erasure        S
open import OpenCalculus.Syntax.Raw            S

------------------------------------------------------------------------
-- Conversions

record Conversion : Set₁ where
  field
    Adm      : ∀ {Θ} → Hyps Θ → Set
    adm-wkᵉ  : ∀ {Θ} {Q : Hyps Θ} → Adm Q → Adm (wkᵉ-H Q)
    Rel      : ∀ {Θ} → Hyps Θ → OVType Θ → OVType Θ → Set
    rel-sub  : ∀ {Θ} {Q : Hyps Θ} {A' A} → Rel Q A' A → Q ∣ A' <:̂ᵛ A
    rel-ok   : ∀ {Θ} {Q : Hyps Θ} {A' A ρ} → Adm Q → Rel Q A' A → VarOK Q A ρ → VarOK Q A' ρ
    rel-box  : ∀ {Θ} {Q : Hyps Θ} {ρ' ρ X' X} → Rel Q ([ ρ' ] X') ([ ρ ] X) → Rel Q X' X
    rel-refl : ∀ {Θ} {Q : Hyps Θ} → (A : OVType Θ) → Rel Q A A
    rel-wkᵉ  : ∀ {Θ} {Q : Hyps Θ} {A' A} → Rel Q A' A → Rel (wkᵉ-H Q) (wkᵉ-v A') (wkᵉ-v A)

-- Mutual subtyping, under any hypotheses

equivalence : Conversion
equivalence = record
  { Adm      = λ _ → ⊤
  ; adm-wkᵉ  = λ _ → tt
  ; Rel      = λ Q A' A → (Q ∣ A' <:̂ᵛ A) × (Q ∣ A <:̂ᵛ A')
  ; rel-sub  = proj₁
  ; rel-ok   = λ _ r → VarOK-≃ (proj₁ r) (proj₂ r) ⊩≾̂ᵣ-refl
  ; rel-box  = λ r → <:̂ᵛ-box-type (proj₁ r) , <:̂ᵛ-box-type (proj₂ r)
  ; rel-refl = λ A → <:̂ᵛ-refl A , <:̂ᵛ-refl A
  ; rel-wkᵉ  = λ r → <:̂ᵛ-wkᵉ (proj₁ r) , <:̂ᵛ-wkᵉ (proj₂ r)
  }

-- Subtyping, under hypotheses with no `disj` hypothesis, where the side
-- condition of `var` reads the type only through eternality

narrowing : Conversion
narrowing = record
  { Adm      = λ Q → disj Q ≡ []
  ; adm-wkᵉ  = λ e → cong (map _) e
  ; Rel      = λ Q A' A → Q ∣ A' <:̂ᵛ A
  ; rel-sub  = λ p → p
  ; rel-ok   = ok
  ; rel-box  = <:̂ᵛ-box-type
  ; rel-refl = <:̂ᵛ-refl
  ; rel-wkᵉ  = <:̂ᵛ-wkᵉ
  }
  where
    ok : ∀ {Θ} {Q : Hyps Θ} {A' A ρ} → disj Q ≡ [] → Q ∣ A' <:̂ᵛ A → VarOK Q A ρ → VarOK Q A' ρ
    ok e p (et-ok et)         = et-ok (<:̂ᵛ-eternalˡ p et)
    ok e p (≾ᵘ-ok le)         = ≾ᵘ-ok le
    ok e p (hyp-ok m _ _ _) with subst (_ ∈_) e m
    ... | ()

------------------------------------------------------------------------
-- Converting a derivation

module _ (𝒞 : Conversion) where

  open Conversion 𝒞

  -- Contexts related pointwise

  data CtxRel {Θ : Scope} (Q : Hyps Θ) : ∀ {n} → OCtx Θ n → OCtx Θ n → Set where
    base  : ∀ {Γ : OCtx Θ 0} → CtxRel Q Γ Γ
    _∷ʳ_  : ∀ {n} {Γ' Γ : OCtx Θ n} {A' A}
          → CtxRel Q Γ' Γ → Rel Q A' A → CtxRel Q (Γ' ∷ A') (Γ ∷ A)
    lockʳ : ∀ {n} {Γ' Γ : OCtx Θ n} {ρ}
          → CtxRel Q Γ' Γ → CtxRel Q (Γ' ⟨ ρ ⟩) (Γ ⟨ ρ ⟩)

  infixl 31 _∷ʳ_

  crel-refl : ∀ {Θ n} {Q : Hyps Θ} → (Γ : OCtx Θ n) → CtxRel Q Γ Γ
  crel-refl []        = base
  crel-refl (Δ ▶ s)   = base
  crel-refl (Γ ∷ A)   = crel-refl Γ ∷ʳ rel-refl A
  crel-refl (Γ ⟨ ρ ⟩) = lockʳ (crel-refl Γ)

  private

    _∷≡_ : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} → CtxRel Q Γ' Γ → (A : OVType Θ)
         → CtxRel Q (Γ' ∷ A) (Γ ∷ A)
    c ∷≡ A = c ∷ʳ rel-refl A

    infixl 31 _∷≡_

    crel-defs : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} → CtxRel Q Γ' Γ → defs Γ' ≡ defs Γ
    crel-defs base      = refl
    crel-defs (c ∷ʳ _)  = crel-defs c
    crel-defs (lockʳ c) = crel-defs c

    crel-wkᵉ : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n}
             → CtxRel Q Γ' Γ → CtxRel (wkᵉ-H Q) (wkᵉ-ctx Γ') (wkᵉ-ctx Γ)
    crel-wkᵉ base      = base
    crel-wkᵉ (c ∷ʳ r)  = crel-wkᵉ c ∷ʳ rel-wkᵉ r
    crel-wkᵉ (lockʳ c) = lockʳ (crel-wkᵉ c)

    no-var : ∀ {Θ} {Γ : OCtx Θ 0} {A ρ} {P : Set} → A ∈̂[ ρ ] Γ → P
    no-var x with var-pos x
    ... | ()

  -- The image of a variable

  record Image {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} (c : CtxRel Q Γ' Γ)
               {A : OVType Θ} {ρ : RExp Θ} (x : A ∈̂[ ρ ] Γ) : Set where
    field
      ty'  : OVType Θ
      mem' : ty' ∈̂[ ρ ] Γ'
      rel' : Rel Q ty' A
      pos' : var-pos mem' ≡ var-pos x

  open Image

  image : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} {A ρ}
        → (c : CtxRel Q Γ' Γ) → (x : A ∈̂[ ρ ] Γ) → Image c x
  image base      x         = no-var x
  image (c ∷ʳ r)  Hd        = record { ty' = _ ; mem' = Hd ; rel' = r ; pos' = refl }
  image (c ∷ʳ r)  (Tl-∷ x)  =
    record { ty' = ty' i ; mem' = Tl-∷ (mem' i) ; rel' = rel' i ; pos' = cong suc (pos' i) }
    where i = image c x
  image (lockʳ c) (Tl-⟨⟩ x) =
    record { ty' = ty' i ; mem' = Tl-⟨⟩ (mem' i) ; rel' = rel' i ; pos' = pos' i }
    where i = image c x

  -- A resource value over a variable of a related box type, reaching a
  -- related box type, with the same erasure

  record ResImage {Θ n} (Q : Hyps Θ) (Γ' : OCtx Θ n) (ρ' : RExp Θ) {ρ₀ X₀}
                  (z' : [ ρ₀ ] X₀ ∈̂[ ρ' ] Γ') (ρ : RExp Θ) (X : OVType Θ) (V : RawV Θ n)
                  : Set where
    field
      {ρ*} : RExp Θ
      {X*} : OVType Θ
      chain* : Q ∣ Γ' ⊢↪[ ρ' ] z' ⦂[ ρ* ] X*
      rel*   : Rel Q ([ ρ* ] X*) ([ ρ ] X)
      erase* : ⌊ chain* ⌋ʳ ≡ V

  open ResImage

  res-image : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} {ρ' ρ₀ ρ₀' ρ : RExp Θ} {X₀ X₀' X : OVType Θ}
                {z : [ ρ₀ ] X₀ ∈̂[ ρ' ] Γ} {z' : [ ρ₀' ] X₀' ∈̂[ ρ' ] Γ'}
            → var-pos z' ≡ var-pos z → Rel Q ([ ρ₀' ] X₀') ([ ρ₀ ] X₀)
            → (R : Q ∣ Γ ⊢↪[ ρ' ] z ⦂[ ρ ] X) → ResImage Q Γ' ρ' z' ρ X ⌊ R ⌋ʳ
  res-image e r₀ res-var = record { chain* = res-var ; rel* = r₀ ; erase* = cong var e }
  res-image e r₀ (res-ann ρₐ Xₐ R p q) =
    record { chain* = res-ann ρₐ Xₐ (chain* i) (transᵣ p (<:̂ᵛ-box-grade s))
                              (<:̂ᵛ-trans (<:̂ᵛ-box-type s) q)
           ; rel*   = rel-refl _
           ; erase* = cong (_⦂ᵛ [ ρₐ ] Xₐ) (erase* i) }
    where
      i = res-image e r₀ R
      s = rel-sub (rel* i)

  -- The image of a variable of box type is a variable of box type

  record BoxImage {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} (c : CtxRel Q Γ' Γ)
                  {ρ₀ X₀ ρ'} (z : [ ρ₀ ] X₀ ∈̂[ ρ' ] Γ) : Set where
    field
      {ρ₀'} : RExp Θ
      {X₀'} : OVType Θ
      z'    : [ ρ₀' ] X₀' ∈̂[ ρ' ] Γ'
      zpos  : var-pos z' ≡ var-pos z
      zrel  : Rel Q ([ ρ₀' ] X₀') ([ ρ₀ ] X₀)

  open BoxImage

  box-image : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} {ρ₀ X₀ ρ'}
            → (c : CtxRel Q Γ' Γ) → (z : [ ρ₀ ] X₀ ∈̂[ ρ' ] Γ) → BoxImage c z
  box-image {Q = Q} {ρ₀ = ρ₀} {X₀} c z =
    record { z'   = ∈̂-ty-subst e (mem' i)
           ; zpos = trans (var-pos-ty-subst e (mem' i)) (pos' i)
           ; zrel = subst (λ T → Rel Q T ([ ρ₀ ] X₀)) e (rel' i) }
    where
      i = image c z
      b = <:̂ᵛ-boxʳ (rel-sub (rel' i))
      e = proj₁ (proj₂ (proj₂ b))

  mutual

    conv-v : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} {A : OVType Θ}
           → Adm Q → CtxRel Q Γ' Γ → Q ∣ Γ ⊢V⦂ A → Q ∣ Γ' ⊢V⦂ A
    conv-v a c (var x ok)      =
      subV (var (mem' i) (rel-ok a (rel' i) ok)) (rel-sub (rel' i))
      where i = image c x
    conv-v a c (def f δ h e)   = def (subst (_ ∈ᵖ[ _ ]_) (sym (crel-defs c)) f) δ h e
    conv-v a c (const B k)     = const B k
    conv-v a c ⋆               = ⋆
    conv-v a c true            = true
    conv-v a c false           = false
    conv-v a c zero            = zero
    conv-v a c (succ V)        = succ (conv-v a c V)
    conv-v a c ⦉ V , W ⦊        = ⦉ conv-v a c V , conv-v a c W ⦊
    conv-v a c (inl V)         = inl (conv-v a c V)
    conv-v a c (inr V)         = inr (conv-v a c V)
    conv-v a c nil             = nil
    conv-v a c (cons V W)      = cons (conv-v a c V) (conv-v a c W)
    conv-v a c (cmp ⋈ V W et)  = cmp ⋈ (conv-v a c V) (conv-v a c W) et
    conv-v a c (lam {A = A} M) = lam (conv-c a (c ∷≡ A) M)
    conv-v a c (handler {A = A} N H) =
      handler (conv-c a (lockʳ c ∷≡ A) N)
              (λ op → conv-c (adm-wkᵉ a) (lockʳ (crel-wkᵉ c) ∷≡ _ ∷≡ _) (H op))
    conv-v a c (annᵛ A V)      = annᵛ A (conv-v a c V)
    conv-v a c (subV V p)      = subV (conv-v a c V) p

    conv-c : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} {C : OCType Θ}
           → Adm Q → CtxRel Q Γ' Γ → Q ∣ Γ ⊢C⦂ C → Q ∣ Γ' ⊢C⦂ C
    conv-c a c (return V)                = return (conv-v a c V)
    conv-c a c (_⨟_ {A = A} M N)         = conv-c a c M ⨟ conv-c a (lockʳ c ∷≡ A) N
    conv-c a c (V · W)                   = conv-v a c V · conv-v a c W
    conv-c a c (match_`in_ {A = A} {B} V M) = match conv-v a c V `in conv-c a (c ∷≡ A ∷≡ B) M
    conv-c a c (absurd V)                = absurd (conv-v a c V)
    conv-c a c (if V `then M `else N)    = if conv-v a c V `then conv-c a c M `else conv-c a c N
    conv-c a c (caseℕ V `zero M `succ N) =
      caseℕ conv-v a c V `zero conv-c a c M `succ conv-c a (c ∷≡ Nat) N
    conv-c a c (case+_`inl_`inr_ {A = A} {B} V M N) =
      case+ conv-v a c V `inl conv-c a (c ∷≡ A) M `inr conv-c a (c ∷≡ B) N
    conv-c a c (caseL_`nil_`cons_ {A = A} V M N) =
      caseL conv-v a c V `nil conv-c a c M `cons conv-c a (c ∷≡ A ∷≡ |List| A) N
    conv-c a c (recℕ {B = B} V M N p)    =
      recℕ (conv-v a c V) (conv-c a c M) (conv-c a (lockʳ (lockʳ c ∷≡ Nat) ∷≡ B) N) p
    conv-c a c (recL {A = A} {B} V M N p) =
      recL (conv-v a c V) (conv-c a c M)
           (conv-c a (lockʳ (lockʳ c ∷≡ A ∷≡ |List| A) ∷≡ B) N) p
    conv-c a c (perform op V M)          = perform op (conv-v a c V) (conv-c a (lockʳ c ∷≡ _) M)
    conv-c a c (delay τ M)               = delay τ (conv-c a (lockʳ c) M)
    conv-c a c (handle M `with V)        = handle conv-c a c M `with conv-v a c V
    conv-c a c (unbox {z = z} R p N)     =
      unbox (chain* r) (transᵣ p (<:̂ᵛ-box-grade (rel-sub (rel* r))))
            (conv-c a (c ∷ʳ rel-box (rel* r)) N)
      where
        b = box-image c z
        r = res-image {z' = z' b} (zpos b) (zrel b) R
    conv-c a c (box {A = A} ρ V N)       = box ρ (conv-v a (lockʳ c) V) (conv-c a (c ∷≡ [ ρ ] A) N)
    conv-c a c (annᶜ C M)                = annᶜ C (conv-c a c M)
    conv-c a c (subC M p)                = subC (conv-c a c M) p

  -- The converted derivation has the same erasure

  mutual

    ⌊conv-v⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} {A : OVType Θ}
             → (a : Adm Q) → (c : CtxRel Q Γ' Γ) → (V : Q ∣ Γ ⊢V⦂ A)
             → ⌊ conv-v a c V ⌋ᵛ ≡ ⌊ V ⌋ᵛ
    ⌊conv-v⌋ a c (var x ok)      = cong var (pos' (image c x))
    ⌊conv-v⌋ a c (def f δ h e)   = refl
    ⌊conv-v⌋ a c (const B k)     = refl
    ⌊conv-v⌋ a c ⋆               = refl
    ⌊conv-v⌋ a c true            = refl
    ⌊conv-v⌋ a c false           = refl
    ⌊conv-v⌋ a c zero            = refl
    ⌊conv-v⌋ a c (succ V)        = cong succ (⌊conv-v⌋ a c V)
    ⌊conv-v⌋ a c ⦉ V , W ⦊        = cong₂ ⦉_,_⦊ (⌊conv-v⌋ a c V) (⌊conv-v⌋ a c W)
    ⌊conv-v⌋ a c (inl V)         = cong inl (⌊conv-v⌋ a c V)
    ⌊conv-v⌋ a c (inr V)         = cong inr (⌊conv-v⌋ a c V)
    ⌊conv-v⌋ a c nil             = refl
    ⌊conv-v⌋ a c (cons V W)      = cong₂ cons (⌊conv-v⌋ a c V) (⌊conv-v⌋ a c W)
    ⌊conv-v⌋ a c (cmp ⋈ V W et)  = cong₂ (cmp ⋈) (⌊conv-v⌋ a c V) (⌊conv-v⌋ a c W)
    ⌊conv-v⌋ a c (lam {A = A} M) = cong lam (⌊conv-c⌋ a (c ∷≡ A) M)
    ⌊conv-v⌋ a c (handler {A = A} N H) =
      cong₂ handler (⌊conv-c⌋ a (lockʳ c ∷≡ A) N)
            (fun-ext (λ op → ⌊conv-c⌋ (adm-wkᵉ a) (lockʳ (crel-wkᵉ c) ∷≡ _ ∷≡ _) (H op)))
    ⌊conv-v⌋ a c (annᵛ A V)      = cong (_⦂ᵛ A) (⌊conv-v⌋ a c V)
    ⌊conv-v⌋ a c (subV V p)      = ⌊conv-v⌋ a c V

    ⌊conv-c⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} {C : OCType Θ}
             → (a : Adm Q) → (c : CtxRel Q Γ' Γ) → (M : Q ∣ Γ ⊢C⦂ C)
             → ⌊ conv-c a c M ⌋ᶜ ≡ ⌊ M ⌋ᶜ
    ⌊conv-c⌋ a c (return V)                = cong return (⌊conv-v⌋ a c V)
    ⌊conv-c⌋ a c (_⨟_ {A = A} M N)         =
      cong₂ _⨟_ (⌊conv-c⌋ a c M) (⌊conv-c⌋ a (lockʳ c ∷≡ A) N)
    ⌊conv-c⌋ a c (V · W)                   = cong₂ _·_ (⌊conv-v⌋ a c V) (⌊conv-v⌋ a c W)
    ⌊conv-c⌋ a c (match_`in_ {A = A} {B} V M) =
      cong₂ match_`in_ (⌊conv-v⌋ a c V) (⌊conv-c⌋ a (c ∷≡ A ∷≡ B) M)
    ⌊conv-c⌋ a c (absurd V)                = cong absurd (⌊conv-v⌋ a c V)
    ⌊conv-c⌋ a c (if V `then M `else N)    =
      cong₃ if_`then_`else_ (⌊conv-v⌋ a c V) (⌊conv-c⌋ a c M) (⌊conv-c⌋ a c N)
    ⌊conv-c⌋ a c (caseℕ V `zero M `succ N) =
      cong₃ caseℕ_`zero_`succ_ (⌊conv-v⌋ a c V) (⌊conv-c⌋ a c M) (⌊conv-c⌋ a (c ∷≡ Nat) N)
    ⌊conv-c⌋ a c (case+_`inl_`inr_ {A = A} {B} V M N) =
      cong₃ case+_`inl_`inr_ (⌊conv-v⌋ a c V) (⌊conv-c⌋ a (c ∷≡ A) M) (⌊conv-c⌋ a (c ∷≡ B) N)
    ⌊conv-c⌋ a c (caseL_`nil_`cons_ {A = A} V M N) =
      cong₃ caseL_`nil_`cons_ (⌊conv-v⌋ a c V) (⌊conv-c⌋ a c M)
            (⌊conv-c⌋ a (c ∷≡ A ∷≡ |List| A) N)
    ⌊conv-c⌋ a c (recℕ {B = B} V M N p)    =
      cong₃ recℕ (⌊conv-v⌋ a c V) (⌊conv-c⌋ a c M) (⌊conv-c⌋ a (lockʳ (lockʳ c ∷≡ Nat) ∷≡ B) N)
    ⌊conv-c⌋ a c (recL {A = A} {B} V M N p) =
      cong₃ recL (⌊conv-v⌋ a c V) (⌊conv-c⌋ a c M)
            (⌊conv-c⌋ a (lockʳ (lockʳ c ∷≡ A ∷≡ |List| A) ∷≡ B) N)
    ⌊conv-c⌋ a c (perform op V M)          =
      cong₂ (perform op) (⌊conv-v⌋ a c V) (⌊conv-c⌋ a (lockʳ c ∷≡ _) M)
    ⌊conv-c⌋ a c (delay τ M)               = cong (delay τ) (⌊conv-c⌋ a (lockʳ c) M)
    ⌊conv-c⌋ a c (handle M `with V)        =
      cong₂ handle_`with_ (⌊conv-c⌋ a c M) (⌊conv-v⌋ a c V)
    ⌊conv-c⌋ a c (unbox {z = z} R p N)     =
      cong₂ unbox (erase* r) (⌊conv-c⌋ a (c ∷ʳ rel-box (rel* r)) N)
      where
        b = box-image c z
        r = res-image {z' = z' b} (zpos b) (zrel b) R
    ⌊conv-c⌋ a c (box {A = A} ρ V N)       =
      cong₂ (box ρ) (⌊conv-v⌋ a (lockʳ c) V) (⌊conv-c⌋ a (c ∷≡ [ ρ ] A) N)
    ⌊conv-c⌋ a c (annᶜ C M)                = cong (_⦂ᶜ C) (⌊conv-c⌋ a c M)
    ⌊conv-c⌋ a c (subC M p)                = ⌊conv-c⌋ a c M

  -- The type of the last variable converted

  conv-last : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A' A : OVType Θ} {C : OCType Θ}
            → Adm Q → Rel Q A' A → (M : Q ∣ Γ ∷ A ⊢C⦂ C)
            → Σ[ M' ∈ Q ∣ Γ ∷ A' ⊢C⦂ C ] ⌊ M' ⌋ᶜ ≡ ⌊ M ⌋ᶜ
  conv-last {Γ = Γ} a r M = conv-c a (crel-refl Γ ∷ʳ r) M , ⌊conv-c⌋ a (crel-refl Γ ∷ʳ r) M
