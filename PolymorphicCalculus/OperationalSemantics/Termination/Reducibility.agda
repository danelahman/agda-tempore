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

open import Language.GroundTypes Grades BTs using (GType; Base; Unit; Bool; Nat; Empty; _|×|ᵍ_; _|+|ᵍ_; |List|ᵍ; [_]ᵍ_)

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

data MultiStep {n} (S : State n) (M : RunC n) : ∀ {m} → State m → RunC m → Set

syntax MultiStep S M S' M' = ⟨ S ∣ M ⟩↝*⟨ S' ∣ M' ⟩

data MultiStep {n} S M where
  done : ⟨ S ∣ M ⟩↝*⟨ S ∣ M ⟩
  _▸_  : ∀ {k m} {S₁ : State k} {e : S ≤ₛ S₁} {M₁} {S' : State m} {M'}
       → ⟨ S ∣ M ⟩↝[ e ]⟨ S₁ ∣ M₁ ⟩ → ⟨ S₁ ∣ M₁ ⟩↝*⟨ S' ∣ M' ⟩ → ⟨ S ∣ M ⟩↝*⟨ S' ∣ M' ⟩

infixr 5 _▸_ _++*_

ext* : ∀ {n m} {S : State n} {M} {S' : State m} {M'} → ⟨ S ∣ M ⟩↝*⟨ S' ∣ M' ⟩ → S ≤ₛ S'
ext* done                 = ≤ₛ-refl
ext* (_▸_ {e = e} s ms)   = e ⨾ₛ ext* ms

_++*_ : ∀ {n k m} {S : State n} {M} {S₁ : State k} {M₁} {S' : State m} {M'}
      → ⟨ S ∣ M ⟩↝*⟨ S₁ ∣ M₁ ⟩ → ⟨ S₁ ∣ M₁ ⟩↝*⟨ S' ∣ M' ⟩ → ⟨ S ∣ M ⟩↝*⟨ S' ∣ M' ⟩
done     ++* ms' = ms'
(s ▸ ms) ++* ms' = s ▸ (ms ++* ms')

ren-⨾ᶜ : ∀ {n m k} {S : State n} {S' : State m} {S'' : State k}
       → (e : S ≤ₛ S') → (e' : S' ≤ₛ S'') → (M : RunC (suc n))
       → renᶜ (ext (wkₛ e')) (renᶜ (ext (wkₛ e)) M) ≡ renᶜ (ext (wkₛ (e ⨾ₛ e'))) M
ren-⨾ᶜ e e' M = ren-fuseᶜ (ext-fuse (λ i → sym (wkₛ-⨾ e e' i))) M

ren-⨾ᵛ : ∀ {n m k} {S : State n} {S' : State m} {S'' : State k}
       → (e : S ≤ₛ S') → (e' : S' ≤ₛ S'') → (V : RunV n)
       → renᵛ (wkₛ e') (renᵛ (wkₛ e) V) ≡ renᵛ (wkₛ (e ⨾ₛ e')) V
ren-⨾ᵛ e e' V = ren-fuseᵛ (λ i → sym (wkₛ-⨾ e e' i)) V

-- runs under the evaluation contexts

seq* : ∀ {n m} {S : State n} {M} {S' : State m} {M'} {N}
     → (ms : ⟨ S ∣ M ⟩↝*⟨ S' ∣ M' ⟩)
     → ⟨ S ∣ M ⨟ N ⟩↝*⟨ S' ∣ M' ⨟ renᶜ (ext (wkₛ (ext* ms))) N ⟩
seq* {M = M} {N = N} done =
  subst (λ X → ⟨ _ ∣ M ⨟ N ⟩↝*⟨ _ ∣ M ⨟ X ⟩) (sym (ren-idᶜ (ext-id (λ i → refl)) N)) done
seq* {N = N} (_▸_ {e = e} s ms) =
  SEQ-STEP s ▸ subst (λ X → ⟨ _ ∣ _ ⟩↝*⟨ _ ∣ _ ⨟ X ⟩) (ren-⨾ᶜ e (ext* ms) N) (seq* ms)

handle* : ∀ {n m} {S : State n} {M} {S' : State m} {M'} {V}
        → (ms : ⟨ S ∣ M ⟩↝*⟨ S' ∣ M' ⟩)
        → ⟨ S ∣ handle M `with V ⟩↝*⟨ S' ∣ handle M' `with renᵛ (wkₛ (ext* ms)) V ⟩
handle* {M = M} {V = V} done =
  subst (λ X → ⟨ _ ∣ handle M `with V ⟩↝*⟨ _ ∣ handle M `with X ⟩)
        (sym (ren-idᵛ (λ i → refl) V)) done
handle* {V = V} (_▸_ {e = e} s ms) =
  HANDLE-STEP s ▸ subst (λ X → ⟨ _ ∣ _ ⟩↝*⟨ _ ∣ handle _ `with X ⟩) (ren-⨾ᵛ e (ext* ms) V) (handle* ms)

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
  shapeᵛ Unit              = unitˢ
  shapeᵛ Bool              = boolˢ
  shapeᵛ Nat               = natˢ
  shapeᵛ (A |×| B)         = shapeᵛ A ×ˢ shapeᵛ B
  shapeᵛ (A |+| B)         = shapeᵛ A +ˢ shapeᵛ B
  shapeᵛ (|List| A)        = listˢ (shapeᵛ A)
  shapeᵛ Empty             = emptyˢ
  shapeᵛ (A ⇒ C)           = shapeᵛ A ⇒ˢ shapeᶜ C
  shapeᵛ (C ⇛ D)           = shapeᶜ C ⇛ˢ shapeᶜ D
  shapeᵛ ([ ρ ] A)         = □ˢ (shapeᵛ A)

  shapeᶜ : ∀ {Θ} → OCType Θ → Shape
  shapeᶜ (A ‼ ε) = shapeᵛ A

shapeᵍ : GType → Shape
shapeᵍ (Base b)    = baseˢ
shapeᵍ Unit        = unitˢ
shapeᵍ Bool        = boolˢ
shapeᵍ Nat         = natˢ
shapeᵍ Empty       = emptyˢ
shapeᵍ (A |×|ᵍ B)  = shapeᵍ A ×ˢ shapeᵍ B
shapeᵍ (A |+|ᵍ B)  = shapeᵍ A +ˢ shapeᵍ B
shapeᵍ (|List|ᵍ A) = listˢ (shapeᵍ A)
shapeᵍ ([ ρ ]ᵍ A)  = □ˢ (shapeᵍ A)

shape-⌜⌝ : ∀ {Θ} → (A : GType) → shapeᵛ (⌜_⌝ᵍ {Θ} A) ≡ shapeᵍ A
shape-⌜⌝ (Base b)    = refl
shape-⌜⌝ Unit        = refl
shape-⌜⌝ Bool        = refl
shape-⌜⌝ Nat         = refl
shape-⌜⌝ Empty       = refl
shape-⌜⌝ (A |×|ᵍ B)  = cong₂ _×ˢ_ (shape-⌜⌝ A) (shape-⌜⌝ B)
shape-⌜⌝ (A |+|ᵍ B)  = cong₂ _+ˢ_ (shape-⌜⌝ A) (shape-⌜⌝ B)
shape-⌜⌝ (|List|ᵍ A) = cong listˢ (shape-⌜⌝ A)
shape-⌜⌝ ([ ρ ]ᵍ A)  = cong □ˢ (shape-⌜⌝ A)

-- Subtyping and weakening preserve the shape

mutual

  <:-shapeᵛ : ∀ {Θ} {Q : Hyps Θ} {A B} → Q ∣ A <:̂ᵛ B → shapeᵛ A ≡ shapeᵛ B
  <:-shapeᵛ (tvarₛ p)   = refl
  <:-shapeᵛ (Baseₛ p)   = refl
  <:-shapeᵛ Unitₛ       = refl
  <:-shapeᵛ Boolₛ       = refl
  <:-shapeᵛ Natₛ        = refl
  <:-shapeᵛ (p |×|ₛ q)  = cong₂ _×ˢ_ (<:-shapeᵛ p) (<:-shapeᵛ q)
  <:-shapeᵛ (p |+|ₛ q)  = cong₂ _+ˢ_ (<:-shapeᵛ p) (<:-shapeᵛ q)
  <:-shapeᵛ (|List|ₛ p) = cong listˢ (<:-shapeᵛ p)
  <:-shapeᵛ Emptyₛ      = refl
  <:-shapeᵛ (p ⇒ₛ q)    = cong₂ _⇒ˢ_ (sym (<:-shapeᵛ p)) (<:-shapeᶜ q)
  <:-shapeᵛ (p ⇛ₛ q)    = cong₂ _⇛ˢ_ (sym (<:-shapeᶜ p)) (<:-shapeᶜ q)
  <:-shapeᵛ ([ p ]ₛ q)  = cong □ˢ (<:-shapeᵛ q)

  <:-shapeᶜ : ∀ {Θ} {Q : Hyps Θ} {C D} → Q ∣ C <:̂ᶜ D → shapeᶜ C ≡ shapeᶜ D
  <:-shapeᶜ (p ‼ₛ q) = <:-shapeᵛ p

mutual

  wkᵉ-shapeᵛ : ∀ {Θ} → (A : OVType Θ) → shapeᵛ (wkᵉ-v A) ≡ shapeᵛ A
  wkᵉ-shapeᵛ (tvar α)   = refl
  wkᵉ-shapeᵛ (Base b)   = refl
  wkᵉ-shapeᵛ Unit       = refl
  wkᵉ-shapeᵛ Bool       = refl
  wkᵉ-shapeᵛ Nat        = refl
  wkᵉ-shapeᵛ (A |×| B)  = cong₂ _×ˢ_ (wkᵉ-shapeᵛ A) (wkᵉ-shapeᵛ B)
  wkᵉ-shapeᵛ (A |+| B)  = cong₂ _+ˢ_ (wkᵉ-shapeᵛ A) (wkᵉ-shapeᵛ B)
  wkᵉ-shapeᵛ (|List| A) = cong listˢ (wkᵉ-shapeᵛ A)
  wkᵉ-shapeᵛ Empty      = refl
  wkᵉ-shapeᵛ (A ⇒ C)    = cong₂ _⇒ˢ_ (wkᵉ-shapeᵛ A) (wkᵉ-shapeᶜ C)
  wkᵉ-shapeᵛ (C ⇛ D)    = cong₂ _⇛ˢ_ (wkᵉ-shapeᶜ C) (wkᵉ-shapeᶜ D)
  wkᵉ-shapeᵛ ([ ρ ] A)  = cong □ˢ (wkᵉ-shapeᵛ A)

  wkᵉ-shapeᶜ : ∀ {Θ} → (C : OCType Θ) → shapeᶜ (wkᵉ-c C) ≡ shapeᶜ C
  wkᵉ-shapeᶜ (A ‼ ε) = wkᵉ-shapeᵛ A

------------------------------------------------------------------------
-- Reducible values of ground type

VRedᵍ : GType → ∀ {n} → State n → RunV n → Set
VRedᵍ (Base b)      S V          = ⊤
VRedᵍ Unit          S V          = ⊤
VRedᵍ Bool          S V          = BoolView V
VRedᵍ Nat           S zero       = ⊤
VRedᵍ Nat           S (succ V)   = VRedᵍ Nat S V
VRedᵍ Nat           S _          = ⊥
VRedᵍ Empty         S V          = ⊥
VRedᵍ (A |×|ᵍ B)    S ⦉ V , W ⦊   = VRedᵍ A S V × VRedᵍ B S W
VRedᵍ (A |×|ᵍ B)    S _          = ⊥
VRedᵍ (A |+|ᵍ B)    S (inl V)    = VRedᵍ A S V
VRedᵍ (A |+|ᵍ B)    S (inr V)    = VRedᵍ B S V
VRedᵍ (A |+|ᵍ B)    S _          = ⊥
VRedᵍ (|List|ᵍ A)   S nil        = ⊤
VRedᵍ (|List|ᵍ A)   S (cons V W) = VRedᵍ A S V × VRedᵍ (|List|ᵍ A) S W
VRedᵍ (|List|ᵍ A)   S _          = ⊥
VRedᵍ ([ ρ ]ᵍ A)    S (var i)    = VRedᵍ A S (lookupₛ S i)
VRedᵍ ([ ρ ]ᵍ A)    S _          = ⊥

------------------------------------------------------------------------
-- Reducible computations, over a predicate on returned values

data CRed (P : ∀ {n} → State n → RunV n → Set) : ∀ {n} → State n → RunC n → Set where

  cred-ret : ∀ {n m} {S : State n} {M} {S' : State m} {V}
           → ⟨ S ∣ M ⟩↝*⟨ S' ∣ return V ⟩ → P S' V
           → CRed P S M

  cred-op  : ∀ {n m} {S : State n} {M} {S' : State m} {op V K}
           → ⟨ S ∣ M ⟩↝*⟨ S' ∣ perform op V K ⟩
           → VRedᵍ (param op) S' V
           → (∀ {k} {S'' : State k} (e : S' ≤ₛ S'') W → VRedᵍ (arity op) S'' W
              → CRed P S'' (renᶜ (ext (wkₛ e)) K [ W ]₀))
           → CRed P S M

------------------------------------------------------------------------
-- Reducible values

VRed : Shape → ∀ {n} → State n → RunV n → Set
VRed unitˢ      S V             = ⊤
VRed baseˢ      S V             = ⊤
VRed boolˢ      S V             = BoolView V
VRed natˢ       S zero          = ⊤
VRed natˢ       S (succ V)      = VRed natˢ S V
VRed natˢ       S _             = ⊥
VRed emptyˢ     S V             = ⊥
VRed (A ×ˢ B)   S ⦉ V , W ⦊      = VRed A S V × VRed B S W
VRed (A ×ˢ B)   S _             = ⊥
VRed (A +ˢ B)   S (inl V)       = VRed A S V
VRed (A +ˢ B)   S (inr V)       = VRed B S V
VRed (A +ˢ B)   S _             = ⊥
VRed (listˢ A)  S nil           = ⊤
VRed (listˢ A)  S (cons V W)    = VRed A S V × VRed (listˢ A) S W
VRed (listˢ A)  S _             = ⊥
VRed (A ⇒ˢ B)   S (lam M)       =
  ∀ {m} {S' : State m} (e : S ≤ₛ S') W → VRed A S' W
  → CRed (VRed B) S' (renᶜ (ext (wkₛ e)) M [ W ]₀)
VRed (A ⇒ˢ B)   S _             = ⊥
VRed (A ⇛ˢ B)   S (handler N H) =
  ∀ {m} {S' : State m} (e : S ≤ₛ S') M → CRed (VRed A) S' M
  → CRed (VRed B) S' (handle M `with renᵛ (wkₛ e) (handler N H))
VRed (A ⇛ˢ B)   S _             = ⊥
VRed (□ˢ A)     S (var i)       = VRed A S (lookupₛ S i)
VRed (□ˢ A)     S _             = ⊥

------------------------------------------------------------------------
-- Stability under extension of the state

private

  bool-ren : ∀ {n m} {V : RunV n} → (f : Fin n → Fin m) → BoolView V → BoolView (renᵛ f V)
  bool-ren f is-true          = is-true
  bool-ren f is-false         = is-false
  bool-ren f (is-cmp ⋈ V W)   = is-cmp ⋈ _ _

VRedᵍ-mono : ∀ (A : GType) {n m} {S : State n} {S' : State m} (e : S ≤ₛ S') V
           → VRedᵍ A S V → VRedᵍ A S' (renᵛ (wkₛ e) V)
VRedᵍ-mono (Base b)    e V          r         = tt
VRedᵍ-mono Unit        e V          r         = tt
VRedᵍ-mono Bool        e V          r         = bool-ren (wkₛ e) r
VRedᵍ-mono Nat         e zero       r         = tt
VRedᵍ-mono Nat         e (succ V)   r         = VRedᵍ-mono Nat e V r
VRedᵍ-mono (A |×|ᵍ B)  e ⦉ V , W ⦊   (r , r')  = VRedᵍ-mono A e V r , VRedᵍ-mono B e W r'
VRedᵍ-mono (A |+|ᵍ B)  e (inl V)    r         = VRedᵍ-mono A e V r
VRedᵍ-mono (A |+|ᵍ B)  e (inr V)    r         = VRedᵍ-mono B e V r
VRedᵍ-mono (|List|ᵍ A) e nil        r         = tt
VRedᵍ-mono (|List|ᵍ A) e (cons V W) (r , r')  =
  VRedᵍ-mono A e V r , VRedᵍ-mono (|List|ᵍ A) e W r'
VRedᵍ-mono ([ ρ ]ᵍ A)  {S = S} {S'} e (var i) r =
  subst (VRedᵍ A S') (sym (lookupₛ-wk e i)) (VRedᵍ-mono A e (lookupₛ S i) r)

VRed-mono : ∀ (A : Shape) {n m} {S : State n} {S' : State m} (e : S ≤ₛ S') V
          → VRed A S V → VRed A S' (renᵛ (wkₛ e) V)
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
VRed-mono (A ⇒ˢ B)  e (lam M)       r {S' = S''} e' W w  =
  subst (λ X → CRed (VRed B) S'' (X [ W ]₀)) (sym (ren-⨾ᶜ e e' M)) (r (e ⨾ₛ e') W w)
VRed-mono (A ⇛ˢ B)  e (handler N H) r {S' = S''} e' M c  =
  subst (λ X → CRed (VRed B) S'' (handle M `with X)) (sym (ren-⨾ᵛ e e' (handler N H)))
        (r (e ⨾ₛ e') M c)
VRed-mono (□ˢ A)    {S = S} {S'} e (var i) r =
  subst (VRed A S') (sym (lookupₛ-wk e i)) (VRed-mono A e (lookupₛ S i) r)

-- Ground types: the two predicates agree

VRed-ground : ∀ (A : GType) {n} {S : State n} V
            → VRed (shapeᵍ A) S V → VRedᵍ A S V
VRed-ground (Base b)    V          r         = tt
VRed-ground Unit        V          r         = tt
VRed-ground Bool        V          r         = r
VRed-ground Nat         zero       r         = tt
VRed-ground Nat         (succ V)   r         = VRed-ground Nat V r
VRed-ground (A |×|ᵍ B)  ⦉ V , W ⦊   (r , r')  = VRed-ground A V r , VRed-ground B W r'
VRed-ground (A |+|ᵍ B)  (inl V)    r         = VRed-ground A V r
VRed-ground (A |+|ᵍ B)  (inr V)    r         = VRed-ground B V r
VRed-ground (|List|ᵍ A) nil        r         = tt
VRed-ground (|List|ᵍ A) (cons V W) (r , r')  = VRed-ground A V r , VRed-ground (|List|ᵍ A) W r'
VRed-ground ([ ρ ]ᵍ A)  {S = S} (var i) r    = VRed-ground A (lookupₛ S i) r

ground-VRed : ∀ (A : GType) {n} {S : State n} V
            → VRedᵍ A S V → VRed (shapeᵍ A) S V
ground-VRed (Base b)    V          r         = tt
ground-VRed Unit        V          r         = tt
ground-VRed Bool        V          r         = r
ground-VRed Nat         zero       r         = tt
ground-VRed Nat         (succ V)   r         = ground-VRed Nat V r
ground-VRed (A |×|ᵍ B)  ⦉ V , W ⦊   (r , r')  = ground-VRed A V r , ground-VRed B W r'
ground-VRed (A |+|ᵍ B)  (inl V)    r         = ground-VRed A V r
ground-VRed (A |+|ᵍ B)  (inr V)    r         = ground-VRed B V r
ground-VRed (|List|ᵍ A) nil        r         = tt
ground-VRed (|List|ᵍ A) (cons V W) (r , r')  = ground-VRed A V r , ground-VRed (|List|ᵍ A) W r'
ground-VRed ([ ρ ]ᵍ A)  {S = S} (var i) r    = ground-VRed A (lookupₛ S i) r

------------------------------------------------------------------------
-- Closure under expansion

cred-back : ∀ {n k} {P : ∀ {n} → State n → RunV n → Set} {S : State n} {M} {S₁ : State k} {M₁}
          → ⟨ S ∣ M ⟩↝*⟨ S₁ ∣ M₁ ⟩ → CRed P S₁ M₁ → CRed P S M
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

  ren-⨾ᶜ² : ∀ {n m k} {S : State n} {S' : State m} {S'' : State k}
          → (e : S ≤ₛ S') → (e' : S' ≤ₛ S'') → (M : RunC (suc (suc n)))
          → renᶜ (ext (ext (wkₛ e'))) (renᶜ (ext (ext (wkₛ e))) M)
            ≡ renᶜ (ext (ext (wkₛ (e ⨾ₛ e')))) M
  ren-⨾ᶜ² e e' M = ren-fuseᶜ (ext-fuse (ext-fuse (λ i → sym (wkₛ-⨾ e e' i)))) M

  ren-congᵛ : ∀ {n m} {f g : Fin n → Fin m} → (∀ i → f i ≡ g i) → (V : RunV n)
            → renᵛ f V ≡ renᵛ g V
  ren-congᵛ p V = trans (cong (renᵛ _) (sym (ren-idᵛ (λ i → refl) V))) (ren-fuseᵛ p V)

res₁ : ∀ {n} {S : State n} {V} → S ≤ₛ S ∷ₛ V
res₁ = ≤ₛ-res ≤ₛ-refl

------------------------------------------------------------------------
-- Sequencing

cred-seq : ∀ {A : Shape} {P : ∀ {n} → State n → RunV n → Set} {n} {S : State n} {M N}
         → CRed (VRed A) S M
         → (∀ {m} {S' : State m} (e : S ≤ₛ S') W → VRed A S' W
            → CRed P S' (renᶜ (ext (wkₛ e)) N [ W ]₀))
         → CRed P S (M ⨟ N)
cred-seq (cred-ret ms r) kN = cred-back (seq* ms ++* (SEQ-RET ▸ done)) (kN (ext* ms) _ r)
cred-seq {A = A} {P = P} {N = N} (cred-op {op = op} {K = K} ms r k) kN =
  cred-back (seq* ms ++* (SEQ-OP ▸ done)) (cred-op done r cont)
  where
    N₁ = renᶜ (ext (wkₛ (ext* ms))) N

    cont : ∀ {k} {S'' : State k} (e' : _ ≤ₛ S'') W → VRedᵍ (arity op) S'' W
         → CRed P S'' (renᶜ (ext (wkₛ e')) (K ⨟ renᶜ (ext suc) N₁) [ W ]₀)
    cont {S'' = S''} e' W w =
      subst (λ X → CRed P S'' (renᶜ (ext (wkₛ e')) K [ W ]₀ ⨟ X))
            (trans (sym (ren-⨾ᶜ (ext* ms) e' N)) (sym (unusedᶜ (wkₛ e') W N₁)))
            (cred-seq {A = A} (k e' W w)
                      (λ {_} {S'''} e'' W' w' →
                         subst (λ X → CRed P S''' (X [ W' ]₀))
                               (sym (ren-⨾ᶜ (ext* ms ⨾ₛ e') e'' N))
                               (kN ((ext* ms ⨾ₛ e') ⨾ₛ e'') W' w')))

------------------------------------------------------------------------
-- Handling

module _ {A B : Shape} {n₀} {S₀ : State n₀} {N : RunC (suc n₀)} {H : Op → RunC (suc (suc n₀))}

  (hyp-ret : ∀ {m} {S' : State m} (e : S₀ ≤ₛ S') V → VRed A S' V
           → CRed (VRed B) S' (renᶜ (ext (wkₛ e)) N [ V ]₀))

  (hyp-op : ∀ op {m} {S' : State m} (e : S₀ ≤ₛ S') V kv
          → VRedᵍ (param op) S' V
          → VRed (shapeᵍ (arity op) ⇒ˢ B) (S' ∷ₛ kv) (wkᵛ kv)
          → CRed (VRed B) (S' ∷ₛ kv) (renᶜ (ext (ext (wkₛ e))) (H op) [ V ]₁))

  where

  cred-handle : ∀ {n} {S : State n} (e₀ : S₀ ≤ₛ S) {M} → CRed (VRed A) S M
              → CRed (VRed B) S (handle M `with renᵛ (wkₛ e₀) (handler N H))
  cred-handle e₀ (cred-ret {S' = S'} {V = V} ms r) =
    cred-back (handle* ms ++* (HANDLE-RET ▸ done))
              (subst (λ X → CRed (VRed B) S' (X [ V ]₀)) (sym (ren-⨾ᶜ e₀ (ext* ms) N))
                     (hyp-ret (e₀ ⨾ₛ ext* ms) V r))
  cred-handle e₀ (cred-op {S' = S'} {op} {V} {K} ms r k) =
    cred-back (handle* ms ++* (HANDLE-OP ▸ BOX ▸ done))
              (subst (λ X → CRed (VRed B) (S' ∷ₛ kv) (X [ V ]₁))
                     (sym (ren-⨾ᶜ² e₀ (ext* ms) (H op)))
                     (hyp-op op g V kv r kvred))
    where
      g  = e₀ ⨾ₛ ext* ms
      h₁ = renᵛ (wkₛ (ext* ms)) (renᵛ (wkₛ e₀) (handler N H))
      kv = lam (handle K `with wkᵛ h₁)

      kvred : VRed (shapeᵍ (arity op) ⇒ˢ B) (S' ∷ₛ kv) (wkᵛ kv)
      kvred {S' = S''} e' W w =
        subst₂ (λ X Y → CRed (VRed B) S'' (handle X [ W ]₀ `with Y))
               (sym (ren-⨾ᶜ res₁ e' K))
               (trans (sym (ren-⨾ᵛ g (res₁ ⨾ₛ e') (handler N H)))
                 (trans (cong (renᵛ (wkₛ (res₁ ⨾ₛ e'))) (sym (ren-⨾ᵛ e₀ (ext* ms) (handler N H))))
                   (trans (ren-congᵛ (wkₛ-⨾ res₁ e') h₁) (sym (unusedᵛ (wkₛ e') W h₁)))))
               (cred-handle (g ⨾ₛ (res₁ ⨾ₛ e'))
                            (k (res₁ ⨾ₛ e') W (VRed-ground (arity op) W w)))
