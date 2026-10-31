------------------------------------------------------------------
-- Conversion of the types of a context                         --
--                                                              --
-- A conversion lets `A'` replace a context type `A`: a subtype --
-- meeting the side condition of `var` wherever `A` does,       --
-- relating box payloads. Pointwise related contexts type the   --
-- same terms with the same erasure (`conv-v`, `conv-c`).       --
-- Instances: `equivalence` and `narrowing`.                    --
------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Fin using (suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Typing.Conversion (S : LanguageSpec) where

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
open import PolymorphicCalculus.Syntax.Raw                 S

------------------------------------------------------------------------
-- Conversions

record Conversion : Set₁ where
  field
    Rel      : ∀ {Θ} → Hyps Θ → OVType Θ → OVType Θ → Set
    rel-sub  : ∀ {Θ} {Q : Hyps Θ} {A' A} → Rel Q A' A → Q ⊩ A' <:̂ᵛ A
    rel-ok   : ∀ {Θ} {Q : Hyps Θ} {A' A ρ} → Rel Q A' A → Q ⊩ A Et∨≾ᵘ ρ → Q ⊩ A' Et∨≾ᵘ ρ
    rel-box  : ∀ {Θ} {Q : Hyps Θ} {ρ' ρ X' X} → Rel Q ([ ρ' ] X') ([ ρ ] X) → Rel Q X' X
    rel-refl : ∀ {Θ} {Q : Hyps Θ} → (A : OVType Θ) → Rel Q A A
    rel-wkᵉ  : ∀ {Θ} {Q : Hyps Θ} {A' A} → Rel Q A' A → Rel (wkᵉ-H Q) (wkᵉ-v A') (wkᵉ-v A)

-- Mutual subtyping

equivalence : Conversion
equivalence = record
  { Rel      = λ Q A' A → (Q ⊩ A' <:̂ᵛ A) × (Q ⊩ A <:̂ᵛ A')
  ; rel-sub  = proj₁
  ; rel-ok   = λ r → Et∨≾ᵘ-≃ (proj₁ r) (proj₂ r) ⊩≾̂ᵣ-refl
  ; rel-box  = λ r → <:̂ᵛ-box-type (proj₁ r) , <:̂ᵛ-box-type (proj₂ r)
  ; rel-refl = λ A → <:̂ᵛ-refl A , <:̂ᵛ-refl A
  ; rel-wkᵉ  = λ r → <:̂ᵛ-wkᵉ (proj₁ r) , <:̂ᵛ-wkᵉ (proj₂ r)
  }

-- Subtyping

narrowing : Conversion
narrowing = record
  { Rel      = λ Q A' A → Q ⊩ A' <:̂ᵛ A
  ; rel-sub  = λ p → p
  ; rel-ok   = subˡ-ok
  ; rel-box  = <:̂ᵛ-box-type
  ; rel-refl = <:̂ᵛ-refl
  ; rel-wkᵉ  = <:̂ᵛ-wkᵉ
  }

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

  -- A resource value over a related variable, with the same erasure

  record ResImage {Θ n} (Q : Hyps Θ) (Γ' : OCtx Θ n) (ρ' : RExp Θ)
                  (ρ : RExp Θ) (X : OVType Θ) (V : RawV Θ n) : Set where
    field
      {ρ*} : RExp Θ
      {X*} : OVType Θ
      chain* : Q ⊢ [ ρ* ] X* ∈̂[ ρ' ] Γ'
      rel*   : Rel Q ([ ρ* ] X*) ([ ρ ] X)
      erase* : ⌊ chain* ⌋ʳ ≡ V

  open ResImage

  res-image : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} {ρ' ρ₀' ρ : RExp Θ} {X₀' X : OVType Θ}
            → (R : Q ⊢ [ ρ ] X ∈̂[ ρ' ] Γ) → (z' : [ ρ₀' ] X₀' ∈̂[ ρ' ] Γ')
            → var-pos z' ≡ var-pos (res-var-of R)
            → Rel Q ([ ρ₀' ] X₀') ([ res-grade-of R ] res-payload-of R)
            → ResImage Q Γ' ρ' ρ X ⌊ R ⌋ʳ
  res-image (res-var _) z' e r₀ = record { chain* = res-var z' ; rel* = r₀ ; erase* = cong var e }
  res-image (res-ann ρₐ Xₐ R p q) z' e r₀ =
    record { chain* = res-ann ρₐ Xₐ (chain* i) (transᵣ p (<:̂ᵛ-box-grade s))
                              (<:̂ᵛ-trans (<:̂ᵛ-box-type s) q)
           ; rel*   = rel-refl _
           ; erase* = cong (_⦂ᵛ [ ρₐ ] Xₐ) (erase* i) }
    where
      i = res-image R z' e r₀
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
           → CtxRel Q Γ' Γ → Q ∣ Γ ⊢ᵛ⦂ A → Q ∣ Γ' ⊢ᵛ⦂ A
    conv-v c (var x ok)      =
      subV (var (mem' i) (rel-ok (rel' i) ok)) (rel-sub (rel' i))
      where i = image c x
    conv-v c (usedef f δ h e) = usedef (subst (_ ∈ᵖ[ _ ]_) (sym (crel-defs c)) f) δ h e
    conv-v c (const B k)     = const B k
    conv-v c ⋆               = ⋆
    conv-v c true            = true
    conv-v c false           = false
    conv-v c zero            = zero
    conv-v c (succ V)        = succ (conv-v c V)
    conv-v c ⦉ V , W ⦊        = ⦉ conv-v c V , conv-v c W ⦊
    conv-v c (inl V)         = inl (conv-v c V)
    conv-v c (inr V)         = inr (conv-v c V)
    conv-v c nil             = nil
    conv-v c (cons V W)      = cons (conv-v c V) (conv-v c W)
    conv-v c (cmp ⋈ V W et)  = cmp ⋈ (conv-v c V) (conv-v c W) et
    conv-v c (fun {A = A} M) = fun (conv-c (c ∷≡ A) M)
    conv-v c (handler {A = A} N H) =
      handler (conv-c (lockʳ c ∷≡ A) N)
              (λ op → conv-c (lockʳ (crel-wkᵉ c) ∷≡ _ ∷≡ _) (H op))
    conv-v c (annᵛ A V)      = annᵛ A (conv-v c V)
    conv-v c (subV V p)      = subV (conv-v c V) p

    conv-c : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} {C : OCType Θ}
           → CtxRel Q Γ' Γ → Q ∣ Γ ⊢ᶜ⦂ C → Q ∣ Γ' ⊢ᶜ⦂ C
    conv-c c (return V)                  = return (conv-v c V)
    conv-c c (_⨟_ {A = A} M N)           = conv-c c M ⨟ conv-c (lockʳ c ∷≡ A) N
    conv-c c (V · W)                     = conv-v c V · conv-v c W
    conv-c c (match_`with_ {A = A} {B} V M) = match conv-v c V `with conv-c (c ∷≡ A ∷≡ B) M
    conv-c c (absurd V)                  = absurd (conv-v c V)
    conv-c c (if V `then M `else N)      = if conv-v c V `then conv-c c M `else conv-c c N
    conv-c c (matchℕ V `zero M `succ N)  =
      matchℕ conv-v c V `zero conv-c c M `succ conv-c (c ∷≡ nat) N
    conv-c c (match+_`inl_`inr_ {A = A} {B} V M N) =
      match+ conv-v c V `inl conv-c (c ∷≡ A) M `inr conv-c (c ∷≡ B) N
    conv-c c (matchL_`nil_`cons_ {A = A} V M N) =
      matchL conv-v c V `nil conv-c c M `cons conv-c (c ∷≡ A ∷≡ list A) N
    conv-c c (recℕ {B = B} V M N p)    =
      recℕ (conv-v c V) (conv-c c M) (conv-c (lockʳ (lockʳ c ∷≡ nat) ∷≡ B) N) p
    conv-c c (recL {A = A} {B} V M N p) =
      recL (conv-v c V) (conv-c c M)
           (conv-c (lockʳ (lockʳ c ∷≡ A ∷≡ list A) ∷≡ B) N) p
    conv-c c (perform op V M)          = perform op (conv-v c V) (conv-c (lockʳ c ∷≡ _) M)
    conv-c c (delay τ M)               = delay τ (conv-c (lockʳ c) M)
    conv-c c (handle M `with V)        = handle conv-c c M `with conv-v c V
    conv-c c (unbox R p N)             =
      unbox (chain* r) (transᵣ p (<:̂ᵛ-box-grade (rel-sub (rel* r))))
            (conv-c (c ∷ʳ rel-box (rel* r)) N)
      where
        b = box-image c (res-var-of R)
        r = res-image R (z' b) (zpos b) (zrel b)
    conv-c c (box {A = A} ρ V N)       = box ρ (conv-v (lockʳ c) V) (conv-c (c ∷≡ [ ρ ] A) N)
    conv-c c (annᶜ C M)                = annᶜ C (conv-c c M)
    conv-c c (subC M p)                = subC (conv-c c M) p

  -- The converted derivation has the same erasure

  mutual

    ⌊conv-v⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} {A : OVType Θ}
             → (c : CtxRel Q Γ' Γ) → (V : Q ∣ Γ ⊢ᵛ⦂ A)
             → ⌊ conv-v c V ⌋ᵛ ≡ ⌊ V ⌋ᵛ
    ⌊conv-v⌋ c (var x ok)      = cong var (pos' (image c x))
    ⌊conv-v⌋ c (usedef f δ h e) = refl
    ⌊conv-v⌋ c (const B k)     = refl
    ⌊conv-v⌋ c ⋆               = refl
    ⌊conv-v⌋ c true            = refl
    ⌊conv-v⌋ c false           = refl
    ⌊conv-v⌋ c zero            = refl
    ⌊conv-v⌋ c (succ V)        = cong succ (⌊conv-v⌋ c V)
    ⌊conv-v⌋ c ⦉ V , W ⦊        = cong₂ ⦉_,_⦊ (⌊conv-v⌋ c V) (⌊conv-v⌋ c W)
    ⌊conv-v⌋ c (inl V)         = cong inl (⌊conv-v⌋ c V)
    ⌊conv-v⌋ c (inr V)         = cong inr (⌊conv-v⌋ c V)
    ⌊conv-v⌋ c nil             = refl
    ⌊conv-v⌋ c (cons V W)      = cong₂ cons (⌊conv-v⌋ c V) (⌊conv-v⌋ c W)
    ⌊conv-v⌋ c (cmp ⋈ V W et)  = cong₂ (cmp ⋈) (⌊conv-v⌋ c V) (⌊conv-v⌋ c W)
    ⌊conv-v⌋ c (fun {A = A} M) = cong fun (⌊conv-c⌋ (c ∷≡ A) M)
    ⌊conv-v⌋ c (handler {A = A} N H) =
      cong₂ handler (⌊conv-c⌋ (lockʳ c ∷≡ A) N)
            (fun-ext (λ op → ⌊conv-c⌋ (lockʳ (crel-wkᵉ c) ∷≡ _ ∷≡ _) (H op)))
    ⌊conv-v⌋ c (annᵛ A V)      = cong (_⦂ᵛ A) (⌊conv-v⌋ c V)
    ⌊conv-v⌋ c (subV V p)      = ⌊conv-v⌋ c V

    ⌊conv-c⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ' Γ : OCtx Θ n} {C : OCType Θ}
             → (c : CtxRel Q Γ' Γ) → (M : Q ∣ Γ ⊢ᶜ⦂ C)
             → ⌊ conv-c c M ⌋ᶜ ≡ ⌊ M ⌋ᶜ
    ⌊conv-c⌋ c (return V)                  = cong return (⌊conv-v⌋ c V)
    ⌊conv-c⌋ c (_⨟_ {A = A} M N)           =
      cong₂ _⨟_ (⌊conv-c⌋ c M) (⌊conv-c⌋ (lockʳ c ∷≡ A) N)
    ⌊conv-c⌋ c (V · W)                     = cong₂ _·_ (⌊conv-v⌋ c V) (⌊conv-v⌋ c W)
    ⌊conv-c⌋ c (match_`with_ {A = A} {B} V M) =
      cong₂ match_`with_ (⌊conv-v⌋ c V) (⌊conv-c⌋ (c ∷≡ A ∷≡ B) M)
    ⌊conv-c⌋ c (absurd V)                  = cong absurd (⌊conv-v⌋ c V)
    ⌊conv-c⌋ c (if V `then M `else N)      =
      cong₃ if_`then_`else_ (⌊conv-v⌋ c V) (⌊conv-c⌋ c M) (⌊conv-c⌋ c N)
    ⌊conv-c⌋ c (matchℕ V `zero M `succ N)  =
      cong₃ matchℕ_`zero_`succ_ (⌊conv-v⌋ c V) (⌊conv-c⌋ c M) (⌊conv-c⌋ (c ∷≡ nat) N)
    ⌊conv-c⌋ c (match+_`inl_`inr_ {A = A} {B} V M N) =
      cong₃ match+_`inl_`inr_ (⌊conv-v⌋ c V) (⌊conv-c⌋ (c ∷≡ A) M) (⌊conv-c⌋ (c ∷≡ B) N)
    ⌊conv-c⌋ c (matchL_`nil_`cons_ {A = A} V M N) =
      cong₃ matchL_`nil_`cons_ (⌊conv-v⌋ c V) (⌊conv-c⌋ c M)
            (⌊conv-c⌋ (c ∷≡ A ∷≡ list A) N)
    ⌊conv-c⌋ c (recℕ {B = B} V M N p)    =
      cong₃ recℕ (⌊conv-v⌋ c V) (⌊conv-c⌋ c M) (⌊conv-c⌋ (lockʳ (lockʳ c ∷≡ nat) ∷≡ B) N)
    ⌊conv-c⌋ c (recL {A = A} {B} V M N p) =
      cong₃ recL (⌊conv-v⌋ c V) (⌊conv-c⌋ c M)
            (⌊conv-c⌋ (lockʳ (lockʳ c ∷≡ A ∷≡ list A) ∷≡ B) N)
    ⌊conv-c⌋ c (perform op V M)          =
      cong₂ (perform op) (⌊conv-v⌋ c V) (⌊conv-c⌋ (lockʳ c ∷≡ _) M)
    ⌊conv-c⌋ c (delay τ M)               = cong (delay τ) (⌊conv-c⌋ (lockʳ c) M)
    ⌊conv-c⌋ c (handle M `with V)        =
      cong₂ handle_`with_ (⌊conv-c⌋ c M) (⌊conv-v⌋ c V)
    ⌊conv-c⌋ c (unbox R p N)             =
      cong₂ unbox (erase* r) (⌊conv-c⌋ (c ∷ʳ rel-box (rel* r)) N)
      where
        b = box-image c (res-var-of R)
        r = res-image R (z' b) (zpos b) (zrel b)
    ⌊conv-c⌋ c (box {A = A} ρ V N)       =
      cong₂ (box ρ) (⌊conv-v⌋ (lockʳ c) V) (⌊conv-c⌋ (c ∷≡ [ ρ ] A) N)
    ⌊conv-c⌋ c (annᶜ C M)                = cong (_⦂ᶜ C) (⌊conv-c⌋ c M)
    ⌊conv-c⌋ c (subC M p)                = ⌊conv-c⌋ c M

  -- The type of the last variable converted

  conv-last : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A' A : OVType Θ} {C : OCType Θ}
            → Rel Q A' A → (M : Q ∣ Γ ∷ A ⊢ᶜ⦂ C)
            → Σ[ M' ∈ Q ∣ Γ ∷ A' ⊢ᶜ⦂ C ] ⌊ M' ⌋ᶜ ≡ ⌊ M ⌋ᶜ
  conv-last {Γ = Γ} r M = conv-c (crel-refl Γ ∷ʳ r) M , ⌊conv-c⌋ (crel-refl Γ ∷ʳ r) M
