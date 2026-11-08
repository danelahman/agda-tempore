------------------------------------------------------------------
-- The data of a closed type                                    --
--                                                              --
-- `⟪ A ⟫` is the set of data of the closed type `A`:           --
-- constants, booleans, numerals, pairs, injections and lists,  --
-- each denoting a `Datum` by `⌊_⌋ᵈ`. A subtyping acts on data  --
-- by `⟪_⟫ˢ`. In a context of box-typed variables and no        --
-- definitions, a value of eternal type denotes a datum of its  --
-- type (`datum-typed`), and the two values of a comparison     --
-- denote data of one eternal type (`compared-data`).           --
------------------------------------------------------------------

open import Data.Bool.Base using () renaming (Bool to 𝔹; true to tt𝔹; false to ff𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)

open import Language.BaseTypes using (module BaseTypes)
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.OperationalSemantics.Data (S : LanguageSpec) where

open LanguageSpec S
open BaseTypes BTs using (BaseConstants)

open import PolymorphicCalculus.Syntax.Types                   S
open import PolymorphicCalculus.Syntax.Contexts                S
open import PolymorphicCalculus.Hypotheses                     S
open import PolymorphicCalculus.Typing                         S
open import PolymorphicCalculus.Typing.Renaming                S using (∥_∥ᵛ)
open import PolymorphicCalculus.Typing.Inversion               S using (BoxCtx; invV≡)
open import PolymorphicCalculus.Typing.ScopeClosed             S
open import PolymorphicCalculus.Syntax.Run                     S
open import PolymorphicCalculus.OperationalSemantics.State     S
  using (State; StateTyping; toCtx; toCtx-box)
open import PolymorphicCalculus.OperationalSemantics.Reduction S

------------------------------------------------------------------------
-- The data of a closed type

data ⟪_⟫ : OVType ∅ˢ → Set where
  base  : ∀ {b} → BaseConstants b → ⟪ Base b ⟫
  unit  : ⟪ unit ⟫
  bit   : 𝔹 → ⟪ bool ⟫
  numᶻ  : ⟪ nat ⟫
  numˢ  : ⟪ nat ⟫ → ⟪ nat ⟫
  pair  : ∀ {A B} → ⟪ A ⟫ → ⟪ B ⟫ → ⟪ A |×| B ⟫
  left  : ∀ {A B} → ⟪ A ⟫ → ⟪ A |+| B ⟫
  right : ∀ {A B} → ⟪ B ⟫ → ⟪ A |+| B ⟫
  nilᵈ  : ∀ {A} → ⟪ list A ⟫
  consᵈ : ∀ {A} → ⟪ A ⟫ → ⟪ list A ⟫ → ⟪ list A ⟫

-- The datum of a datum of a type

⌊_⌋ᵈ : ∀ {A} → ⟪ A ⟫ → Datum
⌊ base {b} c ⌋ᵈ = base b c
⌊ unit ⌋ᵈ       = unit
⌊ bit x ⌋ᵈ      = bit x
⌊ numᶻ ⌋ᵈ       = numᶻ
⌊ numˢ x ⌋ᵈ     = numˢ ⌊ x ⌋ᵈ
⌊ pair x y ⌋ᵈ   = pair ⌊ x ⌋ᵈ ⌊ y ⌋ᵈ
⌊ left x ⌋ᵈ     = left ⌊ x ⌋ᵈ
⌊ right y ⌋ᵈ    = right ⌊ y ⌋ᵈ
⌊ nilᵈ ⌋ᵈ       = nilᵈ
⌊ consᵈ x xs ⌋ᵈ = consᵈ ⌊ x ⌋ᵈ ⌊ xs ⌋ᵈ

-- The action of a subtyping on data, keeping the datum

⟪_⟫ˢ : ∀ {A A'} → ∅ᴴ ⊩ A <:̂ᵛ A' → ⟪ A ⟫ → ⟪ A' ⟫
⟪ Baseₛ refl ⟫ˢ x            = x
⟪ unitₛ ⟫ˢ      x            = x
⟪ boolₛ ⟫ˢ      x            = x
⟪ natₛ ⟫ˢ       x            = x
⟪ p |×|ₛ q ⟫ˢ   (pair x y)   = pair (⟪ p ⟫ˢ x) (⟪ q ⟫ˢ y)
⟪ p |+|ₛ q ⟫ˢ   (left x)     = left (⟪ p ⟫ˢ x)
⟪ p |+|ₛ q ⟫ˢ   (right y)    = right (⟪ q ⟫ˢ y)
⟪ listₛ p ⟫ˢ    nilᵈ         = nilᵈ
⟪ listₛ p ⟫ˢ    (consᵈ x xs) = consᵈ (⟪ p ⟫ˢ x) (⟪ listₛ p ⟫ˢ xs)
⟪ tvarₛ _ ⟫ˢ    ()
⟪ emptyₛ ⟫ˢ     ()
⟪ _ ⇒ₛ _ ⟫ˢ     ()
⟪ _ ⇛ₛ _ ⟫ˢ     ()
⟪ [ _ ]ₛ _ ⟫ˢ   ()

⟪⟫ˢ-datum : ∀ {A A'} → (p : ∅ᴴ ⊩ A <:̂ᵛ A') → (x : ⟪ A ⟫) → ⌊ ⟪ p ⟫ˢ x ⌋ᵈ ≡ ⌊ x ⌋ᵈ
⟪⟫ˢ-datum (Baseₛ refl) x            = refl
⟪⟫ˢ-datum unitₛ        x            = refl
⟪⟫ˢ-datum boolₛ        x            = refl
⟪⟫ˢ-datum natₛ         x            = refl
⟪⟫ˢ-datum (p |×|ₛ q)   (pair x y)   = cong₂ pair (⟪⟫ˢ-datum p x) (⟪⟫ˢ-datum q y)
⟪⟫ˢ-datum (p |+|ₛ q)   (left x)     = cong left (⟪⟫ˢ-datum p x)
⟪⟫ˢ-datum (p |+|ₛ q)   (right y)    = cong right (⟪⟫ˢ-datum q y)
⟪⟫ˢ-datum (listₛ p)    nilᵈ         = refl
⟪⟫ˢ-datum (listₛ p)    (consᵈ x xs) =
  cong₂ consᵈ (⟪⟫ˢ-datum p x) (⟪⟫ˢ-datum (listₛ p) xs)

------------------------------------------------------------------------
-- The datum of a value of eternal type

-- The data a comparison compares: two data of one eternal type, denoted
-- by its two values

record Compared {n} (V W : RunV n) : Set where
  field
    type      : OVType ∅ˢ
    eternal   : ∅ᴴ ⊩Et type
    lhs       : ⟪ type ⟫
    rhs       : ⟪ type ⟫
    lhs-datum : ⌊ lhs ⌋ᵈ ≡ datum V
    rhs-datum : ⌊ rhs ⌋ᵈ ≡ datum W

module _ {n} {Γ : OCtx ∅ˢ n} (bx : BoxCtx Γ) where

  private

    ¬Et-box : ∀ {ρ} {A : OVType ∅ˢ} → ∅ᴴ ⊩Et [ ρ ] A → ⊥
    ¬Et-box ()

    typed-datum : ∀ {A} → ∅ᴴ ⊩Et A → (D : ∅ᴴ ∣ Γ ⊢ᵛ⦂ A)
                → Σ[ x ∈ ⟪ A ⟫ ] ⌊ x ⌋ᵈ ≡ datum ∥ D ∥ᵛ
    typed-datum et (var x p) =
      ⊥-elim (¬Et-box (subst (∅ᴴ ⊩Et_) (proj₂ (proj₂ (proj₁ bx x))) et))
    typed-datum et (usedef f δ h e) =
      ⊥-elim (∅ᵖ-∌ (subst (_ ∈ᵖ[ _ ]_) (proj₂ bx) f))
    typed-datum et (const B c)   = base c , refl
    typed-datum et ⋆             = unit , refl
    typed-datum et true          = bit tt𝔹 , refl
    typed-datum et false         = bit ff𝔹 , refl
    typed-datum et zero          = numᶻ , refl
    typed-datum et (succ V) with typed-datum et V
    ... | x , e = numˢ x , cong numˢ e
    typed-datum (e₁ |×|ₑ e₂) ⦉ V , W ⦊ with typed-datum e₁ V | typed-datum e₂ W
    ... | x , e | y , e' = pair x y , cong₂ pair e e'
    typed-datum (e₁ |+|ₑ e₂) (inl V) with typed-datum e₁ V
    ... | x , e = left x , cong left e
    typed-datum (e₁ |+|ₑ e₂) (inr V) with typed-datum e₂ V
    ... | y , e = right y , cong right e
    typed-datum et nil           = nilᵈ , refl
    typed-datum (listₑ e) (cons V W) with typed-datum e V | typed-datum (listₑ e) W
    ... | x , e₁ | xs , e₂ = consᵈ x xs , cong₂ consᵈ e₁ e₂
    typed-datum et (cmp ⋈ V W _) = bit _ , refl
    typed-datum () (fun M)
    typed-datum () (handler N H)
    typed-datum et (annᵛ A V)    = typed-datum et V
    typed-datum et (subV V p) with typed-datum (<:̂ᵛ-eternalˡ p et) V
    ... | x , e = ⟪ p ⟫ˢ x , trans (⟪⟫ˢ-datum p x) e

  -- a value of eternal type denotes a datum of its type

  datum-typed : ∀ {A V} → ∅ᴴ ⊩Et A → Γ ⊢ᵛ V ⦂ A → Σ[ x ∈ ⟪ A ⟫ ] ⌊ x ⌋ᵈ ≡ datum V
  datum-typed et (D , refl) = typed-datum et D

  -- the values of a typed comparison denote data of one eternal type

  compared-data : ∀ {⋈ V W T} → Γ ⊢ᵛ cmp ⋈ V W ⦂ T → Compared V W
  compared-data (D , e) with invV≡ D e
  ... | _ , (_ , A , et , DV , DW) , _ with datum-typed et DV | datum-typed et DW
  ... | x , ex | y , ey = record
    { type = A ; eternal = et ; lhs = x ; rhs = y ; lhs-datum = ex ; rhs-datum = ey }

-- The comparisons of a configuration over a typed state

compared-in-state : ∀ {n} {𝕊 : State n} → (Ψ : StateTyping 𝕊) → ∀ {⋈ V W T}
                  → toCtx Ψ ⊢ᵛ cmp ⋈ V W ⦂ T → Compared V W
compared-in-state Ψ = compared-data (toCtx-box Ψ)
