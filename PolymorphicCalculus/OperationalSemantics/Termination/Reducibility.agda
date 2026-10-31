------------------------------------------------------------------------
-- Reducible values and computations                                  --
--                                                                    --
-- A unary logical relation on run-time terms over states, by the     --
-- shape of a type. A computation is reducible (`CRed`) when it       --
-- reduces to a returned reducible value, or to an operation call     --
-- with a reducible parameter and a continuation reducible at every   --
-- extension of the state and reducible result. Reducibility is       --
-- stable under extension of the state, closed under expansion, and   --
-- preserved by sequencing and handling.                              --
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.OperationalSemantics.Termination.Reducibility (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Language.GroundTypes Grades BTs using (GType; Base; unit; bool; nat; empty; _|×|ᵍ_; _|+|ᵍ_; listᵍ; [_]ᵍ_)

open import PolymorphicCalculus.Syntax.Grades                  S
open import PolymorphicCalculus.Syntax.Types                   S
open import PolymorphicCalculus.Hypotheses                     S
open import PolymorphicCalculus.Typing.Inversion               S using (BoolView; is-true; is-false; is-cmp)
open import PolymorphicCalculus.Syntax.Run                     S
open import PolymorphicCalculus.Syntax.Run.Substitution S
open import PolymorphicCalculus.OperationalSemantics.State     S
open import PolymorphicCalculus.OperationalSemantics.Reduction S

------------------------------------------------------------------------
-- Multi-step reduction

data MultiStep {n} (𝕊 : State n) (M : RunC n) : ∀ {m} → State m → RunC m → Set

infix 3 MultiStep
syntax MultiStep 𝕊 M 𝕊' M' = ⟨ 𝕊 ∣ M ⟩⟶*⟨ 𝕊' ∣ M' ⟩

data MultiStep {n} 𝕊 M where
  done : ⟨ 𝕊 ∣ M ⟩⟶*⟨ 𝕊 ∣ M ⟩
  _▸_  : ∀ {k m} {𝕊₁ : State k} {e : 𝕊 ≤ₛ 𝕊₁} {M₁} {𝕊' : State m} {M'}
       → ⟨ 𝕊 ∣ M ⟩⟶[ e ]⟨ 𝕊₁ ∣ M₁ ⟩ → ⟨ 𝕊₁ ∣ M₁ ⟩⟶*⟨ 𝕊' ∣ M' ⟩ → ⟨ 𝕊 ∣ M ⟩⟶*⟨ 𝕊' ∣ M' ⟩

infixr 5 _▸_ _++*_

ext* : ∀ {n m} {𝕊 : State n} {M} {𝕊' : State m} {M'} → ⟨ 𝕊 ∣ M ⟩⟶*⟨ 𝕊' ∣ M' ⟩ → 𝕊 ≤ₛ 𝕊'
ext* done                 = ≤ₛ-refl
ext* (_▸_ {e = e} s ms)   = e ⨾ₛ ext* ms

_++*_ : ∀ {n k m} {𝕊 : State n} {M} {𝕊₁ : State k} {M₁} {𝕊' : State m} {M'}
      → ⟨ 𝕊 ∣ M ⟩⟶*⟨ 𝕊₁ ∣ M₁ ⟩ → ⟨ 𝕊₁ ∣ M₁ ⟩⟶*⟨ 𝕊' ∣ M' ⟩ → ⟨ 𝕊 ∣ M ⟩⟶*⟨ 𝕊' ∣ M' ⟩
done     ++* ms' = ms'
(s ▸ ms) ++* ms' = s ▸ (ms ++* ms')

ren-⨾ᶜ : ∀ {n m k} {𝕊 : State n} {𝕊' : State m} {𝕊'' : State k}
       → (e : 𝕊 ≤ₛ 𝕊') → (e' : 𝕊' ≤ₛ 𝕊'') → (M : RunC (suc n))
       → renᶜ (ext (wkₛ e')) (renᶜ (ext (wkₛ e)) M) ≡ renᶜ (ext (wkₛ (e ⨾ₛ e'))) M
ren-⨾ᶜ e e' M = ren-fuseᶜ (ext-fuse (λ i → sym (wkₛ-⨾ e e' i))) M

ren-⨾ᵛ : ∀ {n m k} {𝕊 : State n} {𝕊' : State m} {𝕊'' : State k}
       → (e : 𝕊 ≤ₛ 𝕊') → (e' : 𝕊' ≤ₛ 𝕊'') → (V : RunV n)
       → renᵛ (wkₛ e') (renᵛ (wkₛ e) V) ≡ renᵛ (wkₛ (e ⨾ₛ e')) V
ren-⨾ᵛ e e' V = ren-fuseᵛ (λ i → sym (wkₛ-⨾ e e' i)) V

-- runs under the evaluation contexts

seq* : ∀ {n m} {𝕊 : State n} {M} {𝕊' : State m} {M'} {N}
     → (ms : ⟨ 𝕊 ∣ M ⟩⟶*⟨ 𝕊' ∣ M' ⟩)
     → ⟨ 𝕊 ∣ M ⨟ N ⟩⟶*⟨ 𝕊' ∣ M' ⨟ renᶜ (ext (wkₛ (ext* ms))) N ⟩
seq* {M = M} {N = N} done =
  subst (λ X → ⟨ _ ∣ M ⨟ N ⟩⟶*⟨ _ ∣ M ⨟ X ⟩) (sym (ren-idᶜ (ext-id (λ i → refl)) N)) done
seq* {N = N} (_▸_ {e = e} s ms) =
  SEQ-STEP s ▸ subst (λ X → ⟨ _ ∣ _ ⟩⟶*⟨ _ ∣ _ ⨟ X ⟩) (ren-⨾ᶜ e (ext* ms) N) (seq* ms)

handle* : ∀ {n m} {𝕊 : State n} {M} {𝕊' : State m} {M'} {V}
        → (ms : ⟨ 𝕊 ∣ M ⟩⟶*⟨ 𝕊' ∣ M' ⟩)
        → ⟨ 𝕊 ∣ handle M `with V ⟩⟶*⟨ 𝕊' ∣ handle M' `with renᵛ (wkₛ (ext* ms)) V ⟩
handle* {M = M} {V = V} done =
  subst (λ X → ⟨ _ ∣ handle M `with V ⟩⟶*⟨ _ ∣ handle M `with X ⟩)
        (sym (ren-idᵛ (λ i → refl) V)) done
handle* {V = V} (_▸_ {e = e} s ms) =
  HANDLE-STEP s ▸ subst (λ X → ⟨ _ ∣ _ ⟩⟶*⟨ _ ∣ handle _ `with X ⟩) (ren-⨾ᵛ e (ext* ms) V) (handle* ms)

------------------------------------------------------------------------
-- Shapes: types with their grades forgotten

infixr 30 _⇒ˢ_ _⇛ˢ_
infixr 32 _×ˢ_ _+ˢ_

data Shape : Set where
  unitˢ baseˢ boolˢ natˢ emptyˢ : Shape
  _×ˢ_ _+ˢ_ _⇒ˢ_ _⇛ˢ_          : Shape → Shape → Shape
  listˢ □ˢ                      : Shape → Shape

mutual

  shapeᵛ : ∀ {Θ} → OVType Θ → Shape
  shapeᵛ (tvar α)          = unitˢ
  shapeᵛ (Base b)          = baseˢ
  shapeᵛ unit              = unitˢ
  shapeᵛ bool              = boolˢ
  shapeᵛ nat               = natˢ
  shapeᵛ (A |×| B)         = shapeᵛ A ×ˢ shapeᵛ B
  shapeᵛ (A |+| B)         = shapeᵛ A +ˢ shapeᵛ B
  shapeᵛ (list A)          = listˢ (shapeᵛ A)
  shapeᵛ empty             = emptyˢ
  shapeᵛ (A ⇒ C)           = shapeᵛ A ⇒ˢ shapeᶜ C
  shapeᵛ (C ⇛ D)           = shapeᶜ C ⇛ˢ shapeᶜ D
  shapeᵛ ([ ρ ] A)         = □ˢ (shapeᵛ A)

  shapeᶜ : ∀ {Θ} → OCType Θ → Shape
  shapeᶜ (A ! ε) = shapeᵛ A

shapeᵍ : GType → Shape
shapeᵍ (Base b)    = baseˢ
shapeᵍ unit        = unitˢ
shapeᵍ bool        = boolˢ
shapeᵍ nat         = natˢ
shapeᵍ empty       = emptyˢ
shapeᵍ (A |×|ᵍ B)  = shapeᵍ A ×ˢ shapeᵍ B
shapeᵍ (A |+|ᵍ B)  = shapeᵍ A +ˢ shapeᵍ B
shapeᵍ (listᵍ A)   = listˢ (shapeᵍ A)
shapeᵍ ([ ρ ]ᵍ A)  = □ˢ (shapeᵍ A)

shape-⌜⌝ : ∀ {Θ} → (A : GType) → shapeᵛ (⌜_⌝ᵍ {Θ} A) ≡ shapeᵍ A
shape-⌜⌝ (Base b)    = refl
shape-⌜⌝ unit        = refl
shape-⌜⌝ bool        = refl
shape-⌜⌝ nat         = refl
shape-⌜⌝ empty       = refl
shape-⌜⌝ (A |×|ᵍ B)  = cong₂ _×ˢ_ (shape-⌜⌝ A) (shape-⌜⌝ B)
shape-⌜⌝ (A |+|ᵍ B)  = cong₂ _+ˢ_ (shape-⌜⌝ A) (shape-⌜⌝ B)
shape-⌜⌝ (listᵍ A)   = cong listˢ (shape-⌜⌝ A)
shape-⌜⌝ ([ ρ ]ᵍ A)  = cong □ˢ (shape-⌜⌝ A)

-- Subtyping and weakening preserve the shape

mutual

  <:-shapeᵛ : ∀ {Θ} {Q : Hyps Θ} {A B} → Q ⊩ A <:̂ᵛ B → shapeᵛ A ≡ shapeᵛ B
  <:-shapeᵛ (tvarₛ p)   = refl
  <:-shapeᵛ (Baseₛ p)   = refl
  <:-shapeᵛ unitₛ       = refl
  <:-shapeᵛ boolₛ       = refl
  <:-shapeᵛ natₛ        = refl
  <:-shapeᵛ (p |×|ₛ q)  = cong₂ _×ˢ_ (<:-shapeᵛ p) (<:-shapeᵛ q)
  <:-shapeᵛ (p |+|ₛ q)  = cong₂ _+ˢ_ (<:-shapeᵛ p) (<:-shapeᵛ q)
  <:-shapeᵛ (listₛ p)   = cong listˢ (<:-shapeᵛ p)
  <:-shapeᵛ emptyₛ      = refl
  <:-shapeᵛ (p ⇒ₛ q)    = cong₂ _⇒ˢ_ (sym (<:-shapeᵛ p)) (<:-shapeᶜ q)
  <:-shapeᵛ (p ⇛ₛ q)    = cong₂ _⇛ˢ_ (sym (<:-shapeᶜ p)) (<:-shapeᶜ q)
  <:-shapeᵛ ([ p ]ₛ q)  = cong □ˢ (<:-shapeᵛ q)

  <:-shapeᶜ : ∀ {Θ} {Q : Hyps Θ} {C D} → Q ⊩ C <:̂ᶜ D → shapeᶜ C ≡ shapeᶜ D
  <:-shapeᶜ (p !ₛ q) = <:-shapeᵛ p

mutual

  wkᵉ-shapeᵛ : ∀ {Θ} → (A : OVType Θ) → shapeᵛ (wkᵉ-v A) ≡ shapeᵛ A
  wkᵉ-shapeᵛ (tvar α)   = refl
  wkᵉ-shapeᵛ (Base b)   = refl
  wkᵉ-shapeᵛ unit       = refl
  wkᵉ-shapeᵛ bool       = refl
  wkᵉ-shapeᵛ nat        = refl
  wkᵉ-shapeᵛ (A |×| B)  = cong₂ _×ˢ_ (wkᵉ-shapeᵛ A) (wkᵉ-shapeᵛ B)
  wkᵉ-shapeᵛ (A |+| B)  = cong₂ _+ˢ_ (wkᵉ-shapeᵛ A) (wkᵉ-shapeᵛ B)
  wkᵉ-shapeᵛ (list A)   = cong listˢ (wkᵉ-shapeᵛ A)
  wkᵉ-shapeᵛ empty      = refl
  wkᵉ-shapeᵛ (A ⇒ C)    = cong₂ _⇒ˢ_ (wkᵉ-shapeᵛ A) (wkᵉ-shapeᶜ C)
  wkᵉ-shapeᵛ (C ⇛ D)    = cong₂ _⇛ˢ_ (wkᵉ-shapeᶜ C) (wkᵉ-shapeᶜ D)
  wkᵉ-shapeᵛ ([ ρ ] A)  = cong □ˢ (wkᵉ-shapeᵛ A)

  wkᵉ-shapeᶜ : ∀ {Θ} → (C : OCType Θ) → shapeᶜ (wkᵉ-c C) ≡ shapeᶜ C
  wkᵉ-shapeᶜ (A ! ε) = wkᵉ-shapeᵛ A

------------------------------------------------------------------------
-- Reducible values of ground type

VRedᵍ : GType → ∀ {n} → State n → RunV n → Set
VRedᵍ (Base b)      𝕊 V          = ⊤
VRedᵍ unit          𝕊 V          = ⊤
VRedᵍ bool          𝕊 V          = BoolView V
VRedᵍ nat           𝕊 zero       = ⊤
VRedᵍ nat           𝕊 (succ V)   = VRedᵍ nat 𝕊 V
VRedᵍ nat           𝕊 _          = ⊥
VRedᵍ empty         𝕊 V          = ⊥
VRedᵍ (A |×|ᵍ B)    𝕊 ⦉ V , W ⦊   = VRedᵍ A 𝕊 V × VRedᵍ B 𝕊 W
VRedᵍ (A |×|ᵍ B)    𝕊 _          = ⊥
VRedᵍ (A |+|ᵍ B)    𝕊 (inl V)    = VRedᵍ A 𝕊 V
VRedᵍ (A |+|ᵍ B)    𝕊 (inr V)    = VRedᵍ B 𝕊 V
VRedᵍ (A |+|ᵍ B)    𝕊 _          = ⊥
VRedᵍ (listᵍ A)     𝕊 nil        = ⊤
VRedᵍ (listᵍ A)     𝕊 (cons V W) = VRedᵍ A 𝕊 V × VRedᵍ (listᵍ A) 𝕊 W
VRedᵍ (listᵍ A)     𝕊 _          = ⊥
VRedᵍ ([ ρ ]ᵍ A)    𝕊 (var i)    = VRedᵍ A 𝕊 (lookupₛ 𝕊 i)
VRedᵍ ([ ρ ]ᵍ A)    𝕊 _          = ⊥

------------------------------------------------------------------------
-- Reducible computations, over a predicate on returned values

data CRed (P : ∀ {n} → State n → RunV n → Set) : ∀ {n} → State n → RunC n → Set where

  cred-ret : ∀ {n m} {𝕊 : State n} {M} {𝕊' : State m} {V}
           → ⟨ 𝕊 ∣ M ⟩⟶*⟨ 𝕊' ∣ return V ⟩ → P 𝕊' V
           → CRed P 𝕊 M

  cred-op  : ∀ {n m} {𝕊 : State n} {M} {𝕊' : State m} {op V K}
           → ⟨ 𝕊 ∣ M ⟩⟶*⟨ 𝕊' ∣ perform op V K ⟩
           → VRedᵍ (param op) 𝕊' V
           → (∀ {k} {𝕊'' : State k} (e : 𝕊' ≤ₛ 𝕊'') W → VRedᵍ (arity op) 𝕊'' W
              → CRed P 𝕊'' (renᶜ (ext (wkₛ e)) K [ W ]₀))
           → CRed P 𝕊 M

------------------------------------------------------------------------
-- Reducible values

VRed : Shape → ∀ {n} → State n → RunV n → Set
VRed unitˢ      𝕊 V             = ⊤
VRed baseˢ      𝕊 V             = ⊤
VRed boolˢ      𝕊 V             = BoolView V
VRed natˢ       𝕊 zero          = ⊤
VRed natˢ       𝕊 (succ V)      = VRed natˢ 𝕊 V
VRed natˢ       𝕊 _             = ⊥
VRed emptyˢ     𝕊 V             = ⊥
VRed (A ×ˢ B)   𝕊 ⦉ V , W ⦊      = VRed A 𝕊 V × VRed B 𝕊 W
VRed (A ×ˢ B)   𝕊 _             = ⊥
VRed (A +ˢ B)   𝕊 (inl V)       = VRed A 𝕊 V
VRed (A +ˢ B)   𝕊 (inr V)       = VRed B 𝕊 V
VRed (A +ˢ B)   𝕊 _             = ⊥
VRed (listˢ A)  𝕊 nil           = ⊤
VRed (listˢ A)  𝕊 (cons V W)    = VRed A 𝕊 V × VRed (listˢ A) 𝕊 W
VRed (listˢ A)  𝕊 _             = ⊥
VRed (A ⇒ˢ B)   𝕊 (fun M)       =
  ∀ {m} {𝕊' : State m} (e : 𝕊 ≤ₛ 𝕊') W → VRed A 𝕊' W
  → CRed (VRed B) 𝕊' (renᶜ (ext (wkₛ e)) M [ W ]₀)
VRed (A ⇒ˢ B)   𝕊 _             = ⊥
VRed (A ⇛ˢ B)   𝕊 (handler N H) =
  ∀ {m} {𝕊' : State m} (e : 𝕊 ≤ₛ 𝕊') M → CRed (VRed A) 𝕊' M
  → CRed (VRed B) 𝕊' (handle M `with renᵛ (wkₛ e) (handler N H))
VRed (A ⇛ˢ B)   𝕊 _             = ⊥
VRed (□ˢ A)     𝕊 (var i)       = VRed A 𝕊 (lookupₛ 𝕊 i)
VRed (□ˢ A)     𝕊 _             = ⊥

------------------------------------------------------------------------
-- Stability under extension of the state

private

  bool-ren : ∀ {n m} {V : RunV n} → (f : Fin n → Fin m) → BoolView V → BoolView (renᵛ f V)
  bool-ren f is-true          = is-true
  bool-ren f is-false         = is-false
  bool-ren f (is-cmp ⋈ V W)   = is-cmp ⋈ _ _

VRedᵍ-mono : ∀ (A : GType) {n m} {𝕊 : State n} {𝕊' : State m} (e : 𝕊 ≤ₛ 𝕊') V
           → VRedᵍ A 𝕊 V → VRedᵍ A 𝕊' (renᵛ (wkₛ e) V)
VRedᵍ-mono (Base b)    e V          r         = tt
VRedᵍ-mono unit        e V          r         = tt
VRedᵍ-mono bool        e V          r         = bool-ren (wkₛ e) r
VRedᵍ-mono nat         e zero       r         = tt
VRedᵍ-mono nat         e (succ V)   r         = VRedᵍ-mono nat e V r
VRedᵍ-mono (A |×|ᵍ B)  e ⦉ V , W ⦊   (r , r')  = VRedᵍ-mono A e V r , VRedᵍ-mono B e W r'
VRedᵍ-mono (A |+|ᵍ B)  e (inl V)    r         = VRedᵍ-mono A e V r
VRedᵍ-mono (A |+|ᵍ B)  e (inr V)    r         = VRedᵍ-mono B e V r
VRedᵍ-mono (listᵍ A)   e nil        r         = tt
VRedᵍ-mono (listᵍ A)   e (cons V W) (r , r')  =
  VRedᵍ-mono A e V r , VRedᵍ-mono (listᵍ A) e W r'
VRedᵍ-mono ([ ρ ]ᵍ A)  {𝕊 = 𝕊} {𝕊'} e (var i) r =
  subst (VRedᵍ A 𝕊') (sym (lookupₛ-wk e i)) (VRedᵍ-mono A e (lookupₛ 𝕊 i) r)

VRed-mono : ∀ (A : Shape) {n m} {𝕊 : State n} {𝕊' : State m} (e : 𝕊 ≤ₛ 𝕊') V
          → VRed A 𝕊 V → VRed A 𝕊' (renᵛ (wkₛ e) V)
VRed-mono unitˢ     e V             r         = tt
VRed-mono baseˢ     e V             r         = tt
VRed-mono boolˢ     e V             r         = bool-ren (wkₛ e) r
VRed-mono natˢ      e zero          r         = tt
VRed-mono natˢ      e (succ V)      r         = VRed-mono natˢ e V r
VRed-mono (A ×ˢ B)  e ⦉ V , W ⦊      (r , r')  = VRed-mono A e V r , VRed-mono B e W r'
VRed-mono (A +ˢ B)  e (inl V)       r         = VRed-mono A e V r
VRed-mono (A +ˢ B)  e (inr V)       r         = VRed-mono B e V r
VRed-mono (listˢ A) e nil           r         = tt
VRed-mono (listˢ A) e (cons V W)    (r , r')  = VRed-mono A e V r , VRed-mono (listˢ A) e W r'
VRed-mono (A ⇒ˢ B)  e (fun M)       r {𝕊' = 𝕊''} e' W w  =
  subst (λ X → CRed (VRed B) 𝕊'' (X [ W ]₀)) (sym (ren-⨾ᶜ e e' M)) (r (e ⨾ₛ e') W w)
VRed-mono (A ⇛ˢ B)  e (handler N H) r {𝕊' = 𝕊''} e' M c  =
  subst (λ X → CRed (VRed B) 𝕊'' (handle M `with X)) (sym (ren-⨾ᵛ e e' (handler N H)))
        (r (e ⨾ₛ e') M c)
VRed-mono (□ˢ A)    {𝕊 = 𝕊} {𝕊'} e (var i) r =
  subst (VRed A 𝕊') (sym (lookupₛ-wk e i)) (VRed-mono A e (lookupₛ 𝕊 i) r)

-- Ground types: the two predicates agree

VRed-ground : ∀ (A : GType) {n} {𝕊 : State n} V
            → VRed (shapeᵍ A) 𝕊 V → VRedᵍ A 𝕊 V
VRed-ground (Base b)    V          r         = tt
VRed-ground unit        V          r         = tt
VRed-ground bool        V          r         = r
VRed-ground nat         zero       r         = tt
VRed-ground nat         (succ V)   r         = VRed-ground nat V r
VRed-ground (A |×|ᵍ B)  ⦉ V , W ⦊   (r , r')  = VRed-ground A V r , VRed-ground B W r'
VRed-ground (A |+|ᵍ B)  (inl V)    r         = VRed-ground A V r
VRed-ground (A |+|ᵍ B)  (inr V)    r         = VRed-ground B V r
VRed-ground (listᵍ A)   nil        r         = tt
VRed-ground (listᵍ A)   (cons V W) (r , r')  = VRed-ground A V r , VRed-ground (listᵍ A) W r'
VRed-ground ([ ρ ]ᵍ A)  {𝕊 = 𝕊} (var i) r    = VRed-ground A (lookupₛ 𝕊 i) r

ground-VRed : ∀ (A : GType) {n} {𝕊 : State n} V
            → VRedᵍ A 𝕊 V → VRed (shapeᵍ A) 𝕊 V
ground-VRed (Base b)    V          r         = tt
ground-VRed unit        V          r         = tt
ground-VRed bool        V          r         = r
ground-VRed nat         zero       r         = tt
ground-VRed nat         (succ V)   r         = ground-VRed nat V r
ground-VRed (A |×|ᵍ B)  ⦉ V , W ⦊   (r , r')  = ground-VRed A V r , ground-VRed B W r'
ground-VRed (A |+|ᵍ B)  (inl V)    r         = ground-VRed A V r
ground-VRed (A |+|ᵍ B)  (inr V)    r         = ground-VRed B V r
ground-VRed (listᵍ A)   nil        r         = tt
ground-VRed (listᵍ A)   (cons V W) (r , r')  = ground-VRed A V r , ground-VRed (listᵍ A) W r'
ground-VRed ([ ρ ]ᵍ A)  {𝕊 = 𝕊} (var i) r    = ground-VRed A (lookupₛ 𝕊 i) r

------------------------------------------------------------------------
-- Closure under expansion

cred-back : ∀ {n k} {P : ∀ {n} → State n → RunV n → Set} {𝕊 : State n} {M} {𝕊₁ : State k} {M₁}
          → ⟨ 𝕊 ∣ M ⟩⟶*⟨ 𝕊₁ ∣ M₁ ⟩ → CRed P 𝕊₁ M₁ → CRed P 𝕊 M
cred-back ms (cred-ret ms' r)    = cred-ret (ms ++* ms') r
cred-back ms (cred-op ms' r k)   = cred-op (ms ++* ms') r k

------------------------------------------------------------------------
-- Substituting for a variable that does not occur

private

  unusedᶜ : ∀ {n m} → (f : Fin n → Fin m) → (W : RunV m) → (X : RunC (suc n))
          → subᶜ 1 W (renᶜ (ext (ext f)) (renᶜ (ext suc) X)) ≡ renᶜ (ext f) X
  unusedᶜ f W X =
    trans (sub-psubᶜ 1 W (renᶜ (ext (ext f)) (renᶜ (ext suc) X)))
          (trans (psub-renᶜ (λ i → refl) (renᶜ (ext suc) X))
                 (trans (psub-renᶜ (λ i → refl) X) (psub-varᶜ pw X)))
    where
      pw : ∀ i → subVar 1 W (ext (ext f) (ext suc i)) ≡ var (ext f i)
      pw zero    = refl
      pw (suc i) = refl

  unusedᵛ : ∀ {n m} → (f : Fin (suc n) → Fin m) → (W : RunV m) → (V : RunV n)
          → subᵛ 0 W (renᵛ (ext f) (renᵛ (ext suc) (wkᵛ V))) ≡ renᵛ (λ i → f (suc i)) V
  unusedᵛ f W V =
    trans (sub-psubᵛ 0 W (renᵛ (ext f) (renᵛ (ext suc) (wkᵛ V))))
          (trans (psub-renᵛ (λ i → refl) (renᵛ (ext suc) (wkᵛ V)))
                 (trans (psub-renᵛ (λ i → refl) (wkᵛ V))
                        (trans (psub-renᵛ (λ i → refl) V) (psub-varᵛ (λ i → refl) V))))

  ren-⨾ᶜ² : ∀ {n m k} {𝕊 : State n} {𝕊' : State m} {𝕊'' : State k}
          → (e : 𝕊 ≤ₛ 𝕊') → (e' : 𝕊' ≤ₛ 𝕊'') → (M : RunC (suc (suc n)))
          → renᶜ (ext (ext (wkₛ e'))) (renᶜ (ext (ext (wkₛ e))) M)
            ≡ renᶜ (ext (ext (wkₛ (e ⨾ₛ e')))) M
  ren-⨾ᶜ² e e' M = ren-fuseᶜ (ext-fuse (ext-fuse (λ i → sym (wkₛ-⨾ e e' i)))) M

  ren-congᵛ : ∀ {n m} {f g : Fin n → Fin m} → (∀ i → f i ≡ g i) → (V : RunV n)
            → renᵛ f V ≡ renᵛ g V
  ren-congᵛ p V = trans (cong (renᵛ _) (sym (ren-idᵛ (λ i → refl) V))) (ren-fuseᵛ p V)

res₁ : ∀ {n} {𝕊 : State n} {V} → 𝕊 ≤ₛ 𝕊 ∷ₛ V
res₁ = ≤ₛ-res ≤ₛ-refl

------------------------------------------------------------------------
-- Sequencing

cred-seq : ∀ {A : Shape} {P : ∀ {n} → State n → RunV n → Set} {n} {𝕊 : State n} {M N}
         → CRed (VRed A) 𝕊 M
         → (∀ {m} {𝕊' : State m} (e : 𝕊 ≤ₛ 𝕊') W → VRed A 𝕊' W
            → CRed P 𝕊' (renᶜ (ext (wkₛ e)) N [ W ]₀))
         → CRed P 𝕊 (M ⨟ N)
cred-seq (cred-ret ms r) kN = cred-back (seq* ms ++* (SEQ-RET ▸ done)) (kN (ext* ms) _ r)
cred-seq {A = A} {P = P} {N = N} (cred-op {op = op} {K = K} ms r k) kN =
  cred-back (seq* ms ++* (SEQ-OP ▸ done)) (cred-op done r cont)
  where
    N₁ = renᶜ (ext (wkₛ (ext* ms))) N

    cont : ∀ {k} {𝕊'' : State k} (e' : _ ≤ₛ 𝕊'') W → VRedᵍ (arity op) 𝕊'' W
         → CRed P 𝕊'' (renᶜ (ext (wkₛ e')) (K ⨟ renᶜ (ext suc) N₁) [ W ]₀)
    cont {𝕊'' = 𝕊''} e' W w =
      subst (λ X → CRed P 𝕊'' (renᶜ (ext (wkₛ e')) K [ W ]₀ ⨟ X))
            (trans (sym (ren-⨾ᶜ (ext* ms) e' N)) (sym (unusedᶜ (wkₛ e') W N₁)))
            (cred-seq {A = A} (k e' W w)
                      (λ {_} {𝕊'''} e'' W' w' →
                         subst (λ X → CRed P 𝕊''' (X [ W' ]₀))
                               (sym (ren-⨾ᶜ (ext* ms ⨾ₛ e') e'' N))
                               (kN ((ext* ms ⨾ₛ e') ⨾ₛ e'') W' w')))

------------------------------------------------------------------------
-- Handling

module _ {A B : Shape} {n₀} {𝕊₀ : State n₀} {N : RunC (suc n₀)} {H : Op → RunC (suc (suc n₀))}

  (hyp-ret : ∀ {m} {𝕊' : State m} (e : 𝕊₀ ≤ₛ 𝕊') V → VRed A 𝕊' V
           → CRed (VRed B) 𝕊' (renᶜ (ext (wkₛ e)) N [ V ]₀))

  (hyp-op : ∀ op {m} {𝕊' : State m} (e : 𝕊₀ ≤ₛ 𝕊') V kv
          → VRedᵍ (param op) 𝕊' V
          → VRed (shapeᵍ (arity op) ⇒ˢ B) (𝕊' ∷ₛ kv) (wkᵛ kv)
          → CRed (VRed B) (𝕊' ∷ₛ kv) (renᶜ (ext (ext (wkₛ e))) (H op) [ V ]₁))

  where

  cred-handle : ∀ {n} {𝕊 : State n} (e₀ : 𝕊₀ ≤ₛ 𝕊) {M} → CRed (VRed A) 𝕊 M
              → CRed (VRed B) 𝕊 (handle M `with renᵛ (wkₛ e₀) (handler N H))
  cred-handle e₀ (cred-ret {𝕊' = 𝕊'} {V = V} ms r) =
    cred-back (handle* ms ++* (HANDLE-RET ▸ done))
              (subst (λ X → CRed (VRed B) 𝕊' (X [ V ]₀)) (sym (ren-⨾ᶜ e₀ (ext* ms) N))
                     (hyp-ret (e₀ ⨾ₛ ext* ms) V r))
  cred-handle e₀ (cred-op {𝕊' = 𝕊'} {op} {V} {K} ms r k) =
    cred-back (handle* ms ++* (HANDLE-OP ▸ BOX ▸ done))
              (subst (λ X → CRed (VRed B) (𝕊' ∷ₛ kv) (X [ V ]₁))
                     (sym (ren-⨾ᶜ² e₀ (ext* ms) (H op)))
                     (hyp-op op g V kv r kvred))
    where
      g  = e₀ ⨾ₛ ext* ms
      h₁ = renᵛ (wkₛ (ext* ms)) (renᵛ (wkₛ e₀) (handler N H))
      kv = fun (handle K `with wkᵛ h₁)

      kvred : VRed (shapeᵍ (arity op) ⇒ˢ B) (𝕊' ∷ₛ kv) (wkᵛ kv)
      kvred {𝕊' = 𝕊''} e' W w =
        subst₂ (λ X Y → CRed (VRed B) 𝕊'' (handle X [ W ]₀ `with Y))
               (sym (ren-⨾ᶜ res₁ e' K))
               (trans (sym (ren-⨾ᵛ g (res₁ ⨾ₛ e') (handler N H)))
                 (trans (cong (renᵛ (wkₛ (res₁ ⨾ₛ e'))) (sym (ren-⨾ᵛ e₀ (ext* ms) (handler N H))))
                   (trans (ren-congᵛ (wkₛ-⨾ res₁ e') h₁) (sym (unusedᵛ (wkₛ e') W h₁)))))
               (cred-handle (g ⨾ₛ (res₁ ⨾ₛ e'))
                            (k (res₁ ⨾ₛ e') W (VRed-ground (arity op) W w)))
