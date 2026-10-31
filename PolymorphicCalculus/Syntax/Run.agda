------------------------------------------------------------------
-- Run-time terms                                               --
--                                                              --
-- Raw terms without grades and annotations (`eraseᵛ`,          --
-- `eraseᶜ`): a box keeps no grade, a handler clause no grade   --
-- variable. `RunV n` and `RunC n` are scoped by `n` term       --
-- variables, de Bruijn indices. Renaming, and substitution of  --
-- a value for the variable at depth `k` (`subᶜ k`).            --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc; _+_)

open import Grades.Base
open import Language.Comparisons using (Cmp)
open import Language.BaseTypes using (module BaseTypes)
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Syntax.Run (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open BaseTypes BTs using (BaseType; BaseConstants)

open import PolymorphicCalculus.Syntax.GradeSubstitution     S using (Subst)
open import PolymorphicCalculus.Syntax.Raw                   S
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S

------------------------------------------------------------------------
-- Syntax

mutual

  data RunV (n : ℕ) : Set where
    var     : Fin n → RunV n
    usedef  : ℕ → RunV n
    const   : (B : BaseType) → BaseConstants B → RunV n
    ⋆       : RunV n
    true    : RunV n
    false   : RunV n
    zero    : RunV n
    succ    : RunV n → RunV n
    ⦉_,_⦊    : RunV n → RunV n → RunV n
    inl     : RunV n → RunV n
    inr     : RunV n → RunV n
    nil     : RunV n
    cons    : RunV n → RunV n → RunV n
    cmp     : Cmp → RunV n → RunV n → RunV n
    fun     : RunC (suc n) → RunV n
    handler : RunC (suc n) → (Op → RunC (suc (suc n))) → RunV n

  data RunC (n : ℕ) : Set where
    return              : RunV n → RunC n
    _⨟_                 : RunC n → RunC (suc n) → RunC n
    _·_                 : RunV n → RunV n → RunC n
    match_`with_        : RunV n → RunC (suc (suc n)) → RunC n
    absurd              : RunV n → RunC n
    if_`then_`else_     : RunV n → RunC n → RunC n → RunC n
    matchℕ_`zero_`succ_ : RunV n → RunC n → RunC (suc n) → RunC n
    match+_`inl_`inr_   : RunV n → RunC (suc n) → RunC (suc n) → RunC n
    matchL_`nil_`cons_  : RunV n → RunC n → RunC (suc (suc n)) → RunC n
    recℕ                : RunV n → RunC n → RunC (suc (suc n)) → RunC n
    recL                : RunV n → RunC n → RunC (suc (suc (suc n))) → RunC n
    perform             : Op → RunV n → RunC (suc n) → RunC n
    delay               : 𝔻 → RunC n → RunC n
    handle_`with_       : RunC n → RunV n → RunC n
    unbox               : RunV n → RunC (suc n) → RunC n
    box                 : RunV n → RunC (suc n) → RunC n

------------------------------------------------------------------------
-- Erasure of grades and annotations

mutual

  eraseᵛ : ∀ {Θ n} → RawV Θ n → RunV n
  eraseᵛ (var i)       = var i
  eraseᵛ (usedef k)    = usedef k
  eraseᵛ (const B c)   = const B c
  eraseᵛ ⋆             = ⋆
  eraseᵛ true          = true
  eraseᵛ false         = false
  eraseᵛ zero          = zero
  eraseᵛ (succ V)      = succ (eraseᵛ V)
  eraseᵛ ⦉ V , W ⦊      = ⦉ eraseᵛ V , eraseᵛ W ⦊
  eraseᵛ (inl V)       = inl (eraseᵛ V)
  eraseᵛ (inr V)       = inr (eraseᵛ V)
  eraseᵛ nil           = nil
  eraseᵛ (cons V W)    = cons (eraseᵛ V) (eraseᵛ W)
  eraseᵛ (cmp ⋈ V W)   = cmp ⋈ (eraseᵛ V) (eraseᵛ W)
  eraseᵛ (fun M)       = fun (eraseᶜ M)
  eraseᵛ (handler N H) = handler (eraseᶜ N) (λ op → eraseᶜ (H op))
  eraseᵛ (V ⦂ᵛ A)      = eraseᵛ V

  eraseᶜ : ∀ {Θ n} → RawC Θ n → RunC n
  eraseᶜ (return V)                 = return (eraseᵛ V)
  eraseᶜ (M ⨟ N)                    = eraseᶜ M ⨟ eraseᶜ N
  eraseᶜ (V · W)                    = eraseᵛ V · eraseᵛ W
  eraseᶜ (match V `with M)          = match eraseᵛ V `with eraseᶜ M
  eraseᶜ (absurd V)                 = absurd (eraseᵛ V)
  eraseᶜ (if V `then M `else N)     = if eraseᵛ V `then eraseᶜ M `else eraseᶜ N
  eraseᶜ (matchℕ V `zero M `succ N) = matchℕ eraseᵛ V `zero eraseᶜ M `succ eraseᶜ N
  eraseᶜ (match+ V `inl M `inr N)   = match+ eraseᵛ V `inl eraseᶜ M `inr eraseᶜ N
  eraseᶜ (matchL V `nil M `cons N)  = matchL eraseᵛ V `nil eraseᶜ M `cons eraseᶜ N
  eraseᶜ (recℕ V M N)               = recℕ (eraseᵛ V) (eraseᶜ M) (eraseᶜ N)
  eraseᶜ (recL V M N)               = recL (eraseᵛ V) (eraseᶜ M) (eraseᶜ N)
  eraseᶜ (perform op V M)           = perform op (eraseᵛ V) (eraseᶜ M)
  eraseᶜ (delay τ M)                = delay τ (eraseᶜ M)
  eraseᶜ (handle M `with V)         = handle eraseᶜ M `with eraseᵛ V
  eraseᶜ (unbox V N)                = unbox (eraseᵛ V) (eraseᶜ N)
  eraseᶜ (box ρ V N)                = box (eraseᵛ V) (eraseᶜ N)
  eraseᶜ (M ⦂ᶜ C)                   = eraseᶜ M

-- Erasure forgets a substitution of types and grades

mutual

  erase-substᵛ : ∀ {Θ Θ' n} → (V : RawV Θ n) → (σ : Subst Θ Θ')
               → eraseᵛ (V [ σ ]ᴿᵛ) ≡ eraseᵛ V
  erase-substᵛ (var i)       σ = refl
  erase-substᵛ (usedef k)    σ = refl
  erase-substᵛ (const B c)   σ = refl
  erase-substᵛ ⋆             σ = refl
  erase-substᵛ true          σ = refl
  erase-substᵛ false         σ = refl
  erase-substᵛ zero          σ = refl
  erase-substᵛ (succ V)      σ = cong succ (erase-substᵛ V σ)
  erase-substᵛ ⦉ V , W ⦊      σ = cong₂ ⦉_,_⦊ (erase-substᵛ V σ) (erase-substᵛ W σ)
  erase-substᵛ (inl V)       σ = cong inl (erase-substᵛ V σ)
  erase-substᵛ (inr V)       σ = cong inr (erase-substᵛ V σ)
  erase-substᵛ nil           σ = refl
  erase-substᵛ (cons V W)    σ = cong₂ cons (erase-substᵛ V σ) (erase-substᵛ W σ)
  erase-substᵛ (cmp ⋈ V W)   σ = cong₂ (cmp ⋈) (erase-substᵛ V σ) (erase-substᵛ W σ)
  erase-substᵛ (fun M)       σ = cong fun (erase-substᶜ M σ)
  erase-substᵛ (handler N H) σ =
    cong₂ handler (erase-substᶜ N σ) (fun-ext (λ op → erase-substᶜ (H op) _))
  erase-substᵛ (V ⦂ᵛ A)      σ = erase-substᵛ V σ

  erase-substᶜ : ∀ {Θ Θ' n} → (M : RawC Θ n) → (σ : Subst Θ Θ')
               → eraseᶜ (M [ σ ]ᴿᶜ) ≡ eraseᶜ M
  erase-substᶜ (return V)                 σ = cong return (erase-substᵛ V σ)
  erase-substᶜ (M ⨟ N)                    σ = cong₂ _⨟_ (erase-substᶜ M σ) (erase-substᶜ N σ)
  erase-substᶜ (V · W)                    σ = cong₂ _·_ (erase-substᵛ V σ) (erase-substᵛ W σ)
  erase-substᶜ (match V `with M)          σ =
    cong₂ match_`with_ (erase-substᵛ V σ) (erase-substᶜ M σ)
  erase-substᶜ (absurd V)                 σ = cong absurd (erase-substᵛ V σ)
  erase-substᶜ (if V `then M `else N)     σ =
    cong₃ if_`then_`else_ (erase-substᵛ V σ) (erase-substᶜ M σ) (erase-substᶜ N σ)
  erase-substᶜ (matchℕ V `zero M `succ N) σ =
    cong₃ matchℕ_`zero_`succ_ (erase-substᵛ V σ) (erase-substᶜ M σ) (erase-substᶜ N σ)
  erase-substᶜ (match+ V `inl M `inr N)   σ =
    cong₃ match+_`inl_`inr_ (erase-substᵛ V σ) (erase-substᶜ M σ) (erase-substᶜ N σ)
  erase-substᶜ (matchL V `nil M `cons N)  σ =
    cong₃ matchL_`nil_`cons_ (erase-substᵛ V σ) (erase-substᶜ M σ) (erase-substᶜ N σ)
  erase-substᶜ (recℕ V M N)               σ =
    cong₃ recℕ (erase-substᵛ V σ) (erase-substᶜ M σ) (erase-substᶜ N σ)
  erase-substᶜ (recL V M N)               σ =
    cong₃ recL (erase-substᵛ V σ) (erase-substᶜ M σ) (erase-substᶜ N σ)
  erase-substᶜ (perform op V M)           σ =
    cong₂ (perform op) (erase-substᵛ V σ) (erase-substᶜ M σ)
  erase-substᶜ (delay τ M)                σ = cong (delay τ) (erase-substᶜ M σ)
  erase-substᶜ (handle M `with V)         σ =
    cong₂ handle_`with_ (erase-substᶜ M σ) (erase-substᵛ V σ)
  erase-substᶜ (unbox V N)                σ = cong₂ unbox (erase-substᵛ V σ) (erase-substᶜ N σ)
  erase-substᶜ (box ρ V N)                σ = cong₂ box (erase-substᵛ V σ) (erase-substᶜ N σ)
  erase-substᶜ (M ⦂ᶜ C)                   σ = erase-substᶜ M σ

------------------------------------------------------------------------
-- Renaming

ext : ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
ext f zero    = zero
ext f (suc i) = suc (f i)

mutual

  renᵛ : ∀ {n m} → (Fin n → Fin m) → RunV n → RunV m
  renᵛ f (var i)       = var (f i)
  renᵛ f (usedef k)    = usedef k
  renᵛ f (const B c)   = const B c
  renᵛ f ⋆             = ⋆
  renᵛ f true          = true
  renᵛ f false         = false
  renᵛ f zero          = zero
  renᵛ f (succ V)      = succ (renᵛ f V)
  renᵛ f ⦉ V , W ⦊      = ⦉ renᵛ f V , renᵛ f W ⦊
  renᵛ f (inl V)       = inl (renᵛ f V)
  renᵛ f (inr V)       = inr (renᵛ f V)
  renᵛ f nil           = nil
  renᵛ f (cons V W)    = cons (renᵛ f V) (renᵛ f W)
  renᵛ f (cmp ⋈ V W)   = cmp ⋈ (renᵛ f V) (renᵛ f W)
  renᵛ f (fun M)       = fun (renᶜ (ext f) M)
  renᵛ f (handler N H) = handler (renᶜ (ext f) N) (λ op → renᶜ (ext (ext f)) (H op))

  renᶜ : ∀ {n m} → (Fin n → Fin m) → RunC n → RunC m
  renᶜ f (return V)                 = return (renᵛ f V)
  renᶜ f (M ⨟ N)                    = renᶜ f M ⨟ renᶜ (ext f) N
  renᶜ f (V · W)                    = renᵛ f V · renᵛ f W
  renᶜ f (match V `with M)          = match renᵛ f V `with renᶜ (ext (ext f)) M
  renᶜ f (absurd V)                 = absurd (renᵛ f V)
  renᶜ f (if V `then M `else N)     = if renᵛ f V `then renᶜ f M `else renᶜ f N
  renᶜ f (matchℕ V `zero M `succ N) = matchℕ renᵛ f V `zero renᶜ f M `succ renᶜ (ext f) N
  renᶜ f (match+ V `inl M `inr N)   =
    match+ renᵛ f V `inl renᶜ (ext f) M `inr renᶜ (ext f) N
  renᶜ f (matchL V `nil M `cons N)  =
    matchL renᵛ f V `nil renᶜ f M `cons renᶜ (ext (ext f)) N
  renᶜ f (recℕ V M N)               = recℕ (renᵛ f V) (renᶜ f M) (renᶜ (ext (ext f)) N)
  renᶜ f (recL V M N)               =
    recL (renᵛ f V) (renᶜ f M) (renᶜ (ext (ext (ext f))) N)
  renᶜ f (perform op V M)           = perform op (renᵛ f V) (renᶜ (ext f) M)
  renᶜ f (delay τ M)                = delay τ (renᶜ f M)
  renᶜ f (handle M `with V)         = handle renᶜ f M `with renᵛ f V
  renᶜ f (unbox V N)                = unbox (renᵛ f V) (renᶜ (ext f) N)
  renᶜ f (box V N)                  = box (renᵛ f V) (renᶜ (ext f) N)

wkᵛ : ∀ {n} → RunV n → RunV (suc n)
wkᵛ = renᵛ suc

wkᶜ : ∀ {n} → RunC n → RunC (suc n)
wkᶜ = renᶜ suc

-- Renaming fuses, and depends only on the renaming's values

ext-fuse : ∀ {n m k} {f : Fin m → Fin k} {g : Fin n → Fin m} {h : Fin n → Fin k}
         → (∀ i → f (g i) ≡ h i) → ∀ i → ext f (ext g i) ≡ ext h i
ext-fuse p zero    = refl
ext-fuse p (suc i) = cong suc (p i)

mutual

  ren-fuseᵛ : ∀ {n m k} {f : Fin m → Fin k} {g : Fin n → Fin m} {h : Fin n → Fin k}
            → (∀ i → f (g i) ≡ h i) → (V : RunV n) → renᵛ f (renᵛ g V) ≡ renᵛ h V
  ren-fuseᵛ p (var i)       = cong var (p i)
  ren-fuseᵛ p (usedef k)    = refl
  ren-fuseᵛ p (const B c)   = refl
  ren-fuseᵛ p ⋆             = refl
  ren-fuseᵛ p true          = refl
  ren-fuseᵛ p false         = refl
  ren-fuseᵛ p zero          = refl
  ren-fuseᵛ p (succ V)      = cong succ (ren-fuseᵛ p V)
  ren-fuseᵛ p ⦉ V , W ⦊      = cong₂ ⦉_,_⦊ (ren-fuseᵛ p V) (ren-fuseᵛ p W)
  ren-fuseᵛ p (inl V)       = cong inl (ren-fuseᵛ p V)
  ren-fuseᵛ p (inr V)       = cong inr (ren-fuseᵛ p V)
  ren-fuseᵛ p nil           = refl
  ren-fuseᵛ p (cons V W)    = cong₂ cons (ren-fuseᵛ p V) (ren-fuseᵛ p W)
  ren-fuseᵛ p (cmp ⋈ V W)   = cong₂ (cmp ⋈) (ren-fuseᵛ p V) (ren-fuseᵛ p W)
  ren-fuseᵛ p (fun M)       = cong fun (ren-fuseᶜ (ext-fuse p) M)
  ren-fuseᵛ p (handler N H) =
    cong₂ handler (ren-fuseᶜ (ext-fuse p) N)
                  (fun-ext (λ op → ren-fuseᶜ (ext-fuse (ext-fuse p)) (H op)))

  ren-fuseᶜ : ∀ {n m k} {f : Fin m → Fin k} {g : Fin n → Fin m} {h : Fin n → Fin k}
            → (∀ i → f (g i) ≡ h i) → (M : RunC n) → renᶜ f (renᶜ g M) ≡ renᶜ h M
  ren-fuseᶜ p (return V)                 = cong return (ren-fuseᵛ p V)
  ren-fuseᶜ p (M ⨟ N)                    =
    cong₂ _⨟_ (ren-fuseᶜ p M) (ren-fuseᶜ (ext-fuse p) N)
  ren-fuseᶜ p (V · W)                    = cong₂ _·_ (ren-fuseᵛ p V) (ren-fuseᵛ p W)
  ren-fuseᶜ p (match V `with M)          =
    cong₂ match_`with_ (ren-fuseᵛ p V) (ren-fuseᶜ (ext-fuse (ext-fuse p)) M)
  ren-fuseᶜ p (absurd V)                 = cong absurd (ren-fuseᵛ p V)
  ren-fuseᶜ p (if V `then M `else N)     =
    cong₃ if_`then_`else_ (ren-fuseᵛ p V) (ren-fuseᶜ p M) (ren-fuseᶜ p N)
  ren-fuseᶜ p (matchℕ V `zero M `succ N) =
    cong₃ matchℕ_`zero_`succ_ (ren-fuseᵛ p V) (ren-fuseᶜ p M) (ren-fuseᶜ (ext-fuse p) N)
  ren-fuseᶜ p (match+ V `inl M `inr N)   =
    cong₃ match+_`inl_`inr_ (ren-fuseᵛ p V) (ren-fuseᶜ (ext-fuse p) M)
                            (ren-fuseᶜ (ext-fuse p) N)
  ren-fuseᶜ p (matchL V `nil M `cons N)  =
    cong₃ matchL_`nil_`cons_ (ren-fuseᵛ p V) (ren-fuseᶜ p M)
                             (ren-fuseᶜ (ext-fuse (ext-fuse p)) N)
  ren-fuseᶜ p (recℕ V M N)               =
    cong₃ recℕ (ren-fuseᵛ p V) (ren-fuseᶜ p M) (ren-fuseᶜ (ext-fuse (ext-fuse p)) N)
  ren-fuseᶜ p (recL V M N)               =
    cong₃ recL (ren-fuseᵛ p V) (ren-fuseᶜ p M)
               (ren-fuseᶜ (ext-fuse (ext-fuse (ext-fuse p))) N)
  ren-fuseᶜ p (perform op V M)           =
    cong₂ (perform op) (ren-fuseᵛ p V) (ren-fuseᶜ (ext-fuse p) M)
  ren-fuseᶜ p (delay τ M)                = cong (delay τ) (ren-fuseᶜ p M)
  ren-fuseᶜ p (handle M `with V)         =
    cong₂ handle_`with_ (ren-fuseᶜ p M) (ren-fuseᵛ p V)
  ren-fuseᶜ p (unbox V N)                = cong₂ unbox (ren-fuseᵛ p V) (ren-fuseᶜ (ext-fuse p) N)
  ren-fuseᶜ p (box V N)                  = cong₂ box (ren-fuseᵛ p V) (ren-fuseᶜ (ext-fuse p) N)

ext-id : ∀ {n} {f : Fin n → Fin n} → (∀ i → f i ≡ i) → ∀ i → ext f i ≡ i
ext-id p zero    = refl
ext-id p (suc i) = cong suc (p i)

mutual

  ren-idᵛ : ∀ {n} {f : Fin n → Fin n} → (∀ i → f i ≡ i) → (V : RunV n) → renᵛ f V ≡ V
  ren-idᵛ p (var i)       = cong var (p i)
  ren-idᵛ p (usedef k)    = refl
  ren-idᵛ p (const B c)   = refl
  ren-idᵛ p ⋆             = refl
  ren-idᵛ p true          = refl
  ren-idᵛ p false         = refl
  ren-idᵛ p zero          = refl
  ren-idᵛ p (succ V)      = cong succ (ren-idᵛ p V)
  ren-idᵛ p ⦉ V , W ⦊      = cong₂ ⦉_,_⦊ (ren-idᵛ p V) (ren-idᵛ p W)
  ren-idᵛ p (inl V)       = cong inl (ren-idᵛ p V)
  ren-idᵛ p (inr V)       = cong inr (ren-idᵛ p V)
  ren-idᵛ p nil           = refl
  ren-idᵛ p (cons V W)    = cong₂ cons (ren-idᵛ p V) (ren-idᵛ p W)
  ren-idᵛ p (cmp ⋈ V W)   = cong₂ (cmp ⋈) (ren-idᵛ p V) (ren-idᵛ p W)
  ren-idᵛ p (fun M)       = cong fun (ren-idᶜ (ext-id p) M)
  ren-idᵛ p (handler N H) =
    cong₂ handler (ren-idᶜ (ext-id p) N) (fun-ext (λ op → ren-idᶜ (ext-id (ext-id p)) (H op)))

  ren-idᶜ : ∀ {n} {f : Fin n → Fin n} → (∀ i → f i ≡ i) → (M : RunC n) → renᶜ f M ≡ M
  ren-idᶜ p (return V)                 = cong return (ren-idᵛ p V)
  ren-idᶜ p (M ⨟ N)                    = cong₂ _⨟_ (ren-idᶜ p M) (ren-idᶜ (ext-id p) N)
  ren-idᶜ p (V · W)                    = cong₂ _·_ (ren-idᵛ p V) (ren-idᵛ p W)
  ren-idᶜ p (match V `with M)          =
    cong₂ match_`with_ (ren-idᵛ p V) (ren-idᶜ (ext-id (ext-id p)) M)
  ren-idᶜ p (absurd V)                 = cong absurd (ren-idᵛ p V)
  ren-idᶜ p (if V `then M `else N)     =
    cong₃ if_`then_`else_ (ren-idᵛ p V) (ren-idᶜ p M) (ren-idᶜ p N)
  ren-idᶜ p (matchℕ V `zero M `succ N) =
    cong₃ matchℕ_`zero_`succ_ (ren-idᵛ p V) (ren-idᶜ p M) (ren-idᶜ (ext-id p) N)
  ren-idᶜ p (match+ V `inl M `inr N)   =
    cong₃ match+_`inl_`inr_ (ren-idᵛ p V) (ren-idᶜ (ext-id p) M) (ren-idᶜ (ext-id p) N)
  ren-idᶜ p (matchL V `nil M `cons N)  =
    cong₃ matchL_`nil_`cons_ (ren-idᵛ p V) (ren-idᶜ p M) (ren-idᶜ (ext-id (ext-id p)) N)
  ren-idᶜ p (recℕ V M N)               =
    cong₃ recℕ (ren-idᵛ p V) (ren-idᶜ p M) (ren-idᶜ (ext-id (ext-id p)) N)
  ren-idᶜ p (recL V M N)               =
    cong₃ recL (ren-idᵛ p V) (ren-idᶜ p M) (ren-idᶜ (ext-id (ext-id (ext-id p))) N)
  ren-idᶜ p (perform op V M)           = cong₂ (perform op) (ren-idᵛ p V) (ren-idᶜ (ext-id p) M)
  ren-idᶜ p (delay τ M)                = cong (delay τ) (ren-idᶜ p M)
  ren-idᶜ p (handle M `with V)         = cong₂ handle_`with_ (ren-idᶜ p M) (ren-idᵛ p V)
  ren-idᶜ p (unbox V N)                = cong₂ unbox (ren-idᵛ p V) (ren-idᶜ (ext-id p) N)
  ren-idᶜ p (box V N)                  = cong₂ box (ren-idᵛ p V) (ren-idᶜ (ext-id p) N)

------------------------------------------------------------------------
-- Substitution of a value for the variable at depth `k`, the value
-- weakened past the `k` variables below it

subVar : ∀ {n} → (k : ℕ) → RunV n → Fin (k + suc n) → RunV (k + n)
subVar zero    V zero    = V
subVar zero    V (suc i) = var i
subVar (suc k) V zero    = var zero
subVar (suc k) V (suc i) = wkᵛ (subVar k V i)

mutual

  subᵛ : ∀ {n} → (k : ℕ) → RunV n → RunV (k + suc n) → RunV (k + n)
  subᵛ k U (var i)       = subVar k U i
  subᵛ k U (usedef j)    = usedef j
  subᵛ k U (const B c)   = const B c
  subᵛ k U ⋆             = ⋆
  subᵛ k U true          = true
  subᵛ k U false         = false
  subᵛ k U zero          = zero
  subᵛ k U (succ V)      = succ (subᵛ k U V)
  subᵛ k U ⦉ V , W ⦊      = ⦉ subᵛ k U V , subᵛ k U W ⦊
  subᵛ k U (inl V)       = inl (subᵛ k U V)
  subᵛ k U (inr V)       = inr (subᵛ k U V)
  subᵛ k U nil           = nil
  subᵛ k U (cons V W)    = cons (subᵛ k U V) (subᵛ k U W)
  subᵛ k U (cmp ⋈ V W)   = cmp ⋈ (subᵛ k U V) (subᵛ k U W)
  subᵛ k U (fun M)       = fun (subᶜ (suc k) U M)
  subᵛ k U (handler N H) = handler (subᶜ (suc k) U N) (λ op → subᶜ (suc (suc k)) U (H op))

  subᶜ : ∀ {n} → (k : ℕ) → RunV n → RunC (k + suc n) → RunC (k + n)
  subᶜ k U (return V)                 = return (subᵛ k U V)
  subᶜ k U (M ⨟ N)                    = subᶜ k U M ⨟ subᶜ (suc k) U N
  subᶜ k U (V · W)                    = subᵛ k U V · subᵛ k U W
  subᶜ k U (match V `with M)          = match subᵛ k U V `with subᶜ (suc (suc k)) U M
  subᶜ k U (absurd V)                 = absurd (subᵛ k U V)
  subᶜ k U (if V `then M `else N)     = if subᵛ k U V `then subᶜ k U M `else subᶜ k U N
  subᶜ k U (matchℕ V `zero M `succ N) =
    matchℕ subᵛ k U V `zero subᶜ k U M `succ subᶜ (suc k) U N
  subᶜ k U (match+ V `inl M `inr N)   =
    match+ subᵛ k U V `inl subᶜ (suc k) U M `inr subᶜ (suc k) U N
  subᶜ k U (matchL V `nil M `cons N)  =
    matchL subᵛ k U V `nil subᶜ k U M `cons subᶜ (suc (suc k)) U N
  subᶜ k U (recℕ V M N)               = recℕ (subᵛ k U V) (subᶜ k U M) (subᶜ (suc (suc k)) U N)
  subᶜ k U (recL V M N)               =
    recL (subᵛ k U V) (subᶜ k U M) (subᶜ (suc (suc (suc k))) U N)
  subᶜ k U (perform op V M)           = perform op (subᵛ k U V) (subᶜ (suc k) U M)
  subᶜ k U (delay τ M)                = delay τ (subᶜ k U M)
  subᶜ k U (handle M `with V)         = handle subᶜ k U M `with subᵛ k U V
  subᶜ k U (unbox V N)                = unbox (subᵛ k U V) (subᶜ (suc k) U N)
  subᶜ k U (box V N)                  = box (subᵛ k U V) (subᶜ (suc k) U N)

-- Substitution at the variables of depth 0, 1 and 2

infixl 40 _[_]₀ _[_]₁ _[_]₂

_[_]₀ : ∀ {n} → RunC (suc n) → RunV n → RunC n
M [ V ]₀ = subᶜ 0 V M

_[_]₁ : ∀ {n} → RunC (suc (suc n)) → RunV n → RunC (suc n)
M [ V ]₁ = subᶜ 1 V M

_[_]₂ : ∀ {n} → RunC (suc (suc (suc n))) → RunV n → RunC (suc (suc n))
M [ V ]₂ = subᶜ 2 V M
