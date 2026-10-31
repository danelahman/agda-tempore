------------------------------------------------------------------------
-- The logical relation: reducible values, computations and stores.   --
--                                                                    --
-- Unary and syntactic, since it only has to deliver weak-head        --
-- normalization; soundness and head-faithfulness are separate.       --
--                                                                    --
-- `CRed` is an inductive family, not a recursion on a measure: `E`   --
-- is an arbitrary preordered monoid, so `op-grade op ·ₑ ε` need not  --
-- exceed `ε`. `VRedᵍ` comes first and `CRed` precedes `VRed`,        --
-- which instantiates it at the smaller predicate.                    --
--                                                                    --
-- All three recurse on a type's skeleton rather than the type, a run --
-- refining the value type as it goes.                                --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.Termination.Reducibility (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec

open import MonomorphicCalculus.Syntax.Contexts        Spec
open import MonomorphicCalculus.Syntax.Terms           Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming        Spec
open import MonomorphicCalculus.Syntax.Substitution    Spec
open import MonomorphicCalculus.Syntax.Types           Spec

open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Renaming.Coherence    Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence     Spec
open import MonomorphicCalculus.Syntax.Terms.Transport       Spec
open import MonomorphicCalculus.Syntax.Substitution.Variables  Spec
open import MonomorphicCalculus.OperationalSemantics.GradedReach Spec
open import MonomorphicCalculus.Syntax.Substitution.Equivalence  Spec

-- A value of box type is a variable under a spine of subsumptions: the spine
-- leaves the variable alone, so the value still names a cell, but at the
-- cell's declared grade and payload type, which its own type only bounds.

val-cell : ∀ {Γ A ρ} → Γ ⊢ᵛ⦂ [ ρ ] A
         → Σ[ ρ₀ ∈ R ] Σ[ A₀ ∈ VType ] Var Γ ([ ρ₀ ] A₀)
val-cell {A = A} {ρ = ρ} (var {ρ = σ} _ x) = ρ , A , σ , x
val-cell (subV V ([ _ ]ₛ _))               = val-cell V

cellᵛ : ∀ {Γ A ρ} → (V : Γ ⊢ᵛ⦂ [ ρ ] A)
      → [ proj₁ (val-cell V) ] proj₁ (proj₂ (val-cell V))
          ∈[ proj₁ (proj₂ (proj₂ (val-cell V))) ] Γ
cellᵛ V = proj₂ (proj₂ (proj₂ (val-cell V)))

-- The cell's declared payload type, and the spine as a single subsumption.

val-typeᵛ : ∀ {Γ A ρ} → Γ ⊢ᵛ⦂ [ ρ ] A → VType
val-typeᵛ V = proj₁ (proj₂ (val-cell V))

val-subᵛ : ∀ {Γ A ρ} → (V : Γ ⊢ᵛ⦂ [ ρ ] A) → val-typeᵛ V <:ᵛ A
val-subᵛ {A = A} (var _ x)   = <:ᵛ-refl A
val-subᵛ (subV V ([ _ ]ₛ p)) = <:ᵛ-trans (val-subᵛ V) p

-- The two projections commute with renaming and with a context equality.
-- Both are one-clause inductions; the variable clause is absurd.

fstᵛ-ren : ∀ {A B} {𝕊 𝕊' : State []} → (r : Ren [] (toCtx 𝕊') (toCtx 𝕊))
         → (V : toCtx 𝕊 ⊢ᵛ⦂ A |×| B)
         → fstᵛ (V-rename r V) ≡ V-rename r (fstᵛ V)
fstᵛ-ren r (var _ x)             = ⊥-elim (⦉⦊-not-in-toCtx x)
fstᵛ-ren r ⦉ _ , _ ⦊             = refl
fstᵛ-ren r (subV V (p |×|ₛ _))   = cong (λ z → subV z p) (fstᵛ-ren r V)

sndᵛ-ren : ∀ {A B} {𝕊 𝕊' : State []} → (r : Ren [] (toCtx 𝕊') (toCtx 𝕊))
         → (V : toCtx 𝕊 ⊢ᵛ⦂ A |×| B)
         → sndᵛ (V-rename r V) ≡ V-rename r (sndᵛ V)
sndᵛ-ren r (var _ x)             = ⊥-elim (⦉⦊-not-in-toCtx x)
sndᵛ-ren r ⦉ _ , _ ⦊             = refl
sndᵛ-ren r (subV V (_ |×|ₛ q))   = cong (λ z → subV z q) (sndᵛ-ren r V)

-- The injection commutes with renaming: the renaming acts on the payload.

ren⊎ : ∀ {Γ Γ' A B} → Ren [] Γ' Γ → (Γ ⊢ᵛ⦂ A) ⊎ (Γ ⊢ᵛ⦂ B) → (Γ' ⊢ᵛ⦂ A) ⊎ (Γ' ⊢ᵛ⦂ B)
ren⊎ r (inj₁ W) = inj₁ (V-rename r W)
ren⊎ r (inj₂ W) = inj₂ (V-rename r W)

injᵛ-ren : ∀ {A B} {𝕊 𝕊' : State []} → (r : Ren [] (toCtx 𝕊') (toCtx 𝕊))
         → (V : toCtx 𝕊 ⊢ᵛ⦂ A |+| B)
         → injᵛ (V-rename r V) ≡ ren⊎ r (injᵛ V)
injᵛ-ren r (var _ x)           = ⊥-elim (|+|-not-in-toCtx x)
injᵛ-ren r (inl V)             = refl
injᵛ-ren r (inr V)             = refl
injᵛ-ren r (subV V (p |+|ₛ q)) =
  trans (cong (sub⊎ p q) (injᵛ-ren r V)) (comm (injᵛ V))
  where
    comm : ∀ s → sub⊎ p q (ren⊎ r s) ≡ ren⊎ r (sub⊎ p q s)
    comm (inj₁ W) = refl
    comm (inj₂ W) = refl

-- The decomposition of a list commutes with renaming: the renaming acts on the
-- head and the tail.

renL : ∀ {Γ Γ' A} → Ren [] Γ' Γ → ListView Γ A → ListView Γ' A
renL r (inj₁ tt)      = inj₁ tt
renL r (inj₂ (W , L)) = inj₂ (V-rename r W , V-rename r L)

listᵛ-ren : ∀ {A} {𝕊 𝕊' : State []} → (r : Ren [] (toCtx 𝕊') (toCtx 𝕊))
          → (V : toCtx 𝕊 ⊢ᵛ⦂ list A)
          → listᵛ (V-rename r V) ≡ renL r (listᵛ V)
listᵛ-ren r (var _ x)            = ⊥-elim (list-not-in-toCtx x)
listᵛ-ren r nil                  = refl
listᵛ-ren r (cons V W)           = refl
listᵛ-ren r (subV V (listₛ p))   =
  trans (cong (subL p) (listᵛ-ren r V)) (comm (listᵛ V))
  where
    comm : ∀ l → subL p (renL r l) ≡ renL r (subL p l)
    comm (inj₁ tt)      = refl
    comm (inj₂ (W , L)) = refl

-- The skeleton a type shares with all its subtypes.

data Shape : Set where
  ⋆ˢ   : Shape
  _×ˢ_ : Shape → Shape → Shape
  _+ˢ_ : Shape → Shape → Shape
  _→ˢ_ : Shape → Shape → Shape
  _⇛ˢ_ : Shape → Shape → Shape
  □ˢ   : Shape → Shape
  Lˢ   : Shape → Shape

shapeᵛ : VType → Shape
shapeᵛ (Base b)      = ⋆ˢ
shapeᵛ unit          = ⋆ˢ
shapeᵛ bool          = ⋆ˢ
shapeᵛ nat           = ⋆ˢ
shapeᵛ (A |×| B)     = shapeᵛ A ×ˢ shapeᵛ B
shapeᵛ (A |+| B)     = shapeᵛ A +ˢ shapeᵛ B
shapeᵛ (list A)      = Lˢ (shapeᵛ A)
shapeᵛ empty         = ⋆ˢ
shapeᵛ (A ⇒ (B ! _)) = shapeᵛ A →ˢ shapeᵛ B
shapeᵛ ((A ! _) ⇛ (B ! _)) = shapeᵛ A ⇛ˢ shapeᵛ B
shapeᵛ ([ _ ] A)     = □ˢ (shapeᵛ A)

×ˢ-inj₁ : ∀ {t t' s s'} → (t ×ˢ t') ≡ (s ×ˢ s') → t ≡ s
×ˢ-inj₁ refl = refl

×ˢ-inj₂ : ∀ {t t' s s'} → (t ×ˢ t') ≡ (s ×ˢ s') → t' ≡ s'
×ˢ-inj₂ refl = refl

+ˢ-inj₁ : ∀ {t t' s s'} → (t +ˢ t') ≡ (s +ˢ s') → t ≡ s
+ˢ-inj₁ refl = refl

+ˢ-inj₂ : ∀ {t t' s s'} → (t +ˢ t') ≡ (s +ˢ s') → t' ≡ s'
+ˢ-inj₂ refl = refl

→ˢ-inj₁ : ∀ {t t' s s'} → (t →ˢ t') ≡ (s →ˢ s') → t ≡ s
→ˢ-inj₁ refl = refl

→ˢ-inj₂ : ∀ {t t' s s'} → (t →ˢ t') ≡ (s →ˢ s') → t' ≡ s'
→ˢ-inj₂ refl = refl

⇛ˢ-inj₁ : ∀ {t t' s s'} → (t ⇛ˢ t') ≡ (s ⇛ˢ s') → t ≡ s
⇛ˢ-inj₁ refl = refl

⇛ˢ-inj₂ : ∀ {t t' s s'} → (t ⇛ˢ t') ≡ (s ⇛ˢ s') → t' ≡ s'
⇛ˢ-inj₂ refl = refl

□ˢ-inj : ∀ {t s} → □ˢ t ≡ □ˢ s → t ≡ s
□ˢ-inj refl = refl

Lˢ-inj : ∀ {t s} → Lˢ t ≡ Lˢ s → t ≡ s
Lˢ-inj refl = refl

<:ᵛ-shape : ∀ {A A'} → A <:ᵛ A' → shapeᵛ A ≡ shapeᵛ A'
<:ᵛ-shape (Baseₛ _)       = refl
<:ᵛ-shape unitₛ           = refl
<:ᵛ-shape boolₛ           = refl
<:ᵛ-shape natₛ            = refl
<:ᵛ-shape (p |×|ₛ q)      = cong₂ _×ˢ_ (<:ᵛ-shape p) (<:ᵛ-shape q)
<:ᵛ-shape (p |+|ₛ q)      = cong₂ _+ˢ_ (<:ᵛ-shape p) (<:ᵛ-shape q)
<:ᵛ-shape (listₛ p)       = cong Lˢ (<:ᵛ-shape p)
<:ᵛ-shape emptyₛ          = refl
<:ᵛ-shape (p ⇒ₛ (q !ₛ _)) = cong₂ _→ˢ_ (sym (<:ᵛ-shape p)) (<:ᵛ-shape q)
<:ᵛ-shape ((p !ₛ _) ⇛ₛ (q !ₛ _)) = cong₂ _⇛ˢ_ (sym (<:ᵛ-shape p)) (<:ᵛ-shape q)
<:ᵛ-shape ([ _ ]ₛ p)      = cong □ˢ (<:ᵛ-shape p)

-- A handler is used as itself, or at a supertype through one subsumption.

data Use {Γ C D} (V : Γ ⊢ᵛ⦂ C ⇛ D) : {C₀ D₀ : CType} → Γ ⊢ᵛ⦂ C₀ ⇛ D₀ → Set where
  use-id  : Use V V
  use-sub : ∀ {C₀ D₀} → (w : C ⇛ D <:ᵛ C₀ ⇛ D₀) → Use V (subV V w)

use-<: : ∀ {Γ C D C₀ D₀} {V : Γ ⊢ᵛ⦂ C ⇛ D} {U : Γ ⊢ᵛ⦂ C₀ ⇛ D₀}
       → Use V U → C ⇛ D <:ᵛ C₀ ⇛ D₀
use-<: use-id      = <:ᵛ-refl _
use-<: (use-sub w) = w

-- The skeletons of the handled and the result type a use stands at.

use-shape₁ : ∀ {Γ A B ε ε' A₀ B₀ ε₀ ε₀' t t'}
             {V : Γ ⊢ᵛ⦂ (A ! ε) ⇛ (B ! ε')} {U : Γ ⊢ᵛ⦂ (A₀ ! ε₀) ⇛ (B₀ ! ε₀')}
           → Use V U → (shapeᵛ A ⇛ˢ shapeᵛ B) ≡ (t ⇛ˢ t') → shapeᵛ A₀ ≡ t
use-shape₁ u e = trans (sym (⇛ˢ-inj₁ (<:ᵛ-shape (use-<: u)))) (⇛ˢ-inj₁ e)

use-shape₂ : ∀ {Γ A B ε ε' A₀ B₀ ε₀ ε₀' t t'}
             {V : Γ ⊢ᵛ⦂ (A ! ε) ⇛ (B ! ε')} {U : Γ ⊢ᵛ⦂ (A₀ ! ε₀) ⇛ (B₀ ! ε₀')}
           → Use V U → (shapeᵛ A ⇛ˢ shapeᵛ B) ≡ (t ⇛ˢ t') → shapeᵛ B₀ ≡ t'
use-shape₂ u e = trans (sym (⇛ˢ-inj₂ (<:ᵛ-shape (use-<: u)))) (⇛ˢ-inj₂ e)

-- A sum is reducible when it is an injection of a reducible payload.

data VRed⊎ {Γ A B} (P : Γ ⊢ᵛ⦂ A → Set) (Q : Γ ⊢ᵛ⦂ B → Set)
     : (Γ ⊢ᵛ⦂ A) ⊎ (Γ ⊢ᵛ⦂ B) → Set where
  red-inl : ∀ {W} → P W → VRed⊎ P Q (inj₁ W)
  red-inr : ∀ {W} → Q W → VRed⊎ P Q (inj₂ W)

-- A list is reducible when its decomposition is empty, or a reducible head
-- and a reducible tail. Inductive: the tail's clause is this one again.

data VRedL {𝕊 : State []} {A} (P : toCtx 𝕊 ⊢ᵛ⦂ A → Set)
     : ListView (toCtx 𝕊) A → Set where
  red-nil  : VRedL P (inj₁ tt)
  red-cons : ∀ {W L} → P W → VRedL P (listᵛ L) → VRedL P (inj₂ (W , L))

-- Reducibility carried across a subsumption of the elements.

VRedL-sub : ∀ {𝕊 : State []} {A A'} {P : toCtx 𝕊 ⊢ᵛ⦂ A → Set}
            {Q : toCtx 𝕊 ⊢ᵛ⦂ A' → Set} → (p : A <:ᵛ A')
          → (∀ W → P W → Q (subV W p))
          → ∀ {l} → VRedL P l → VRedL Q (subL p l)
VRedL-sub p f red-nil          = red-nil
VRedL-sub p f (red-cons pW pL) = red-cons (f _ pW) (VRedL-sub p f pL)

-- Reducibility of sums and lists carried along an implication of the
-- payloads' predicates.

VRed⊎-map : ∀ {Γ A B} {P P' : Γ ⊢ᵛ⦂ A → Set} {Q Q' : Γ ⊢ᵛ⦂ B → Set}
          → (∀ W → P W → P' W) → (∀ W → Q W → Q' W)
          → ∀ {s} → VRed⊎ P Q s → VRed⊎ P' Q' s
VRed⊎-map f g (red-inl p) = red-inl (f _ p)
VRed⊎-map f g (red-inr q) = red-inr (g _ q)

VRedL-map : ∀ {𝕊 : State []} {A} {P Q : toCtx 𝕊 ⊢ᵛ⦂ A → Set}
          → (∀ W → P W → Q W) → ∀ {l} → VRedL P l → VRedL Q l
VRedL-map f red-nil          = red-nil
VRedL-map f (red-cons pW pL) = red-cons (f _ pW) (VRedL-map f pL)

-- Ground types are the parameter and arity types of operations. They contain
-- no arrows, so the arrow clause is vacuous and this needs nothing but itself.

VRedᵍˢ : (t : Shape) → {A : VType} → shapeᵛ A ≡ t
       → (𝕊 : State []) → toCtx 𝕊 ⊢ᵛ⦂ A → Set

VRedᵍˢ ⋆ˢ        e 𝕊 V = ⊤
VRedᵍˢ (t →ˢ t') e 𝕊 V = ⊤
VRedᵍˢ (t ⇛ˢ t') e 𝕊 V = ⊤

VRedᵍˢ (Lˢ t) {list A}       e  𝕊 V =
  VRedL (VRedᵍˢ t (Lˢ-inj e) 𝕊) (listᵛ V)
VRedᵍˢ (Lˢ t) {Base b}      () 𝕊 V
VRedᵍˢ (Lˢ t) {unit}        () 𝕊 V
VRedᵍˢ (Lˢ t) {bool}        () 𝕊 V
VRedᵍˢ (Lˢ t) {nat}         () 𝕊 V
VRedᵍˢ (Lˢ t) {A |×| B}     () 𝕊 V
VRedᵍˢ (Lˢ t) {A |+| B}     () 𝕊 V
VRedᵍˢ (Lˢ t) {empty}       () 𝕊 V
VRedᵍˢ (Lˢ t) {A ⇒ (B ! ε)} () 𝕊 V
VRedᵍˢ (Lˢ t) {(A ! ε) ⇛ (B ! ε')} () 𝕊 V
VRedᵍˢ (Lˢ t) {[ ρ ] A}     () 𝕊 V

VRedᵍˢ (t ×ˢ t') {A |×| B}     e  𝕊 V =
  VRedᵍˢ t (×ˢ-inj₁ e) 𝕊 (fstᵛ V) × VRedᵍˢ t' (×ˢ-inj₂ e) 𝕊 (sndᵛ V)
VRedᵍˢ (t ×ˢ t') {Base b}      () 𝕊 V
VRedᵍˢ (t ×ˢ t') {unit}        () 𝕊 V
VRedᵍˢ (t ×ˢ t') {bool}        () 𝕊 V
VRedᵍˢ (t ×ˢ t') {nat}         () 𝕊 V
VRedᵍˢ (t ×ˢ t') {list A}      () 𝕊 V
VRedᵍˢ (t ×ˢ t') {A |+| B}     () 𝕊 V

VRedᵍˢ (t +ˢ t') {A |+| B}     e  𝕊 V =
  VRed⊎ (VRedᵍˢ t (+ˢ-inj₁ e) 𝕊) (VRedᵍˢ t' (+ˢ-inj₂ e) 𝕊) (injᵛ V)
VRedᵍˢ (t +ˢ t') {Base b}      () 𝕊 V
VRedᵍˢ (t +ˢ t') {unit}        () 𝕊 V
VRedᵍˢ (t +ˢ t') {bool}        () 𝕊 V
VRedᵍˢ (t +ˢ t') {nat}         () 𝕊 V
VRedᵍˢ (t +ˢ t') {list A}      () 𝕊 V
VRedᵍˢ (t +ˢ t') {A |×| B}     () 𝕊 V
VRedᵍˢ (t +ˢ t') {empty}       () 𝕊 V
VRedᵍˢ (t +ˢ t') {A ⇒ (B ! ε)} () 𝕊 V
VRedᵍˢ (t +ˢ t') {(A ! ε) ⇛ (B ! ε')} () 𝕊 V
VRedᵍˢ (t +ˢ t') {[ ρ ] A}     () 𝕊 V
VRedᵍˢ (t ×ˢ t') {empty}       () 𝕊 V
VRedᵍˢ (t ×ˢ t') {A ⇒ (B ! ε)} () 𝕊 V
VRedᵍˢ (t ×ˢ t') {(A ! ε) ⇛ (B ! ε')} () 𝕊 V
VRedᵍˢ (t ×ˢ t') {[ ρ ] A}     () 𝕊 V

VRedᵍˢ (□ˢ t) {[ ρ ] A}     e  𝕊 V =
  ∀ {𝕊'} → (r : 𝕊 [ cellᵛ V ]⊑ᶜ 𝕊')
  → VRedᵍˢ t (trans (<:ᵛ-shape (val-subᵛ V)) (□ˢ-inj e)) 𝕊' (lookupᶜ r)
VRedᵍˢ (□ˢ t) {Base b}      () 𝕊 V
VRedᵍˢ (□ˢ t) {unit}        () 𝕊 V
VRedᵍˢ (□ˢ t) {bool}        () 𝕊 V
VRedᵍˢ (□ˢ t) {nat}         () 𝕊 V
VRedᵍˢ (□ˢ t) {list A}      () 𝕊 V
VRedᵍˢ (□ˢ t) {A |+| B}     () 𝕊 V
VRedᵍˢ (□ˢ t) {A |×| B}     () 𝕊 V
VRedᵍˢ (□ˢ t) {empty}       () 𝕊 V
VRedᵍˢ (□ˢ t) {A ⇒ (B ! ε)} () 𝕊 V
VRedᵍˢ (□ˢ t) {(A ! ε) ⇛ (B ! ε')} () 𝕊 V

VRedᵍ : (G : GType) → (𝕊 : State []) → toCtx 𝕊 ⊢ᵛ⦂ ⌜ G ⌝ᵍ → Set
VRedᵍ G = VRedᵍˢ (shapeᵛ ⌜ G ⌝ᵍ) {⌜ G ⌝ᵍ} refl

-- `M` runs to a weak head normal form whose components are reducible. A step
-- refines the value type as well as the grade, so the whnf's own value type is
-- free and only its skeleton `s` is fixed; the refinement witness is stored as
-- the shape equality the whnf stands at.

VPred : Shape → Set₁
VPred s = {A : VType} → shapeᵛ A ≡ s → (𝕊 : State []) → toCtx 𝕊 ⊢ᵛ⦂ A → Set

data CRed (s : Shape) (P : VPred s)
     : {A : VType} → shapeᵛ A ≡ s
     → (ε : E) → (𝕊 : State []) → toCtx 𝕊 ⊢ᶜ⦂ A ! ε → Set where

  -- it returns a reducible value

  cred-ret : ∀ {A A₀ ε} {e : shapeᵛ A ≡ s} {𝕊 𝕊₁ : State []}
           → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
           → {V : toCtx 𝕊₁ ⊢ᵛ⦂ A₀}
           → (e₀ : shapeᵛ A₀ ≡ s)
           → ⟨ 𝕊 ∣ M ⟩ ⟶* ⟨ 𝕊₁ ∣ return V ⟩
           → P e₀ 𝕊₁ V
           ---------------------------------
           → CRed s P e ε 𝕊 M

  -- or it gets stuck on an operation with a reducible parameter, whose
  -- resumption is reducible at every state where the operation's own grade
  -- has elapsed

  cred-op : ∀ {A A₀ ε ε₁} {e : shapeᵛ A ≡ s} {𝕊 𝕊₁ : State []} {op : Op}
          → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
          → {W : toCtx 𝕊₁ ⊢ᵛ⦂ ⌜ param op ⌝ᵍ}
          → {M' : toCtx 𝕊₁ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
                    ⊢ᶜ⦂ A₀ ! ε₁}
          → (e₀ : shapeᵛ A₀ ≡ s)
          → ⟨ 𝕊 ∣ M ⟩ ⟶* ⟨ 𝕊₁ ∣ perform op W M' ⟩
          → VRedᵍ (param op) 𝕊₁ W
          → (∀ {𝕊₂ : State []}
             → (q : 𝕊₁ ⊑ₛ[ ∣ op-grade op ∣ᵉ ] 𝕊₂)
             → (W' : toCtx 𝕊₂ ⊢ᵛ⦂ ⌜ arity op ⌝ᵍ)
             → VRedᵍ (arity op) 𝕊₂ W'
             → CRed s P e₀ ε₁ 𝕊₂ (resume q M' W'))
          -------------------------------------------------------------------
          → CRed s P e ε 𝕊 M

-- Stated through the eliminators, so that subsumption is absorbed: a product
-- by its two projections, a sum by the injection it is (`injᵛ`) and its
-- payload, a list by its decomposition (`listᵛ`), a function by what it does to a reducible argument
-- at a later state, a handler by what it does to a reducible computation at a
-- later state, a box by what reading its cell yields. `⇒`, `⇛` and `[ ρ ]` are
-- Kripke.

VRedˢ : (t : Shape) → {A : VType} → shapeᵛ A ≡ t
      → (𝕊 : State []) → toCtx 𝕊 ⊢ᵛ⦂ A → Set

VRedˢ ⋆ˢ e 𝕊 V = ⊤

VRedˢ (t ×ˢ t') {A |×| B}     e  𝕊 V =
  VRedˢ t (×ˢ-inj₁ e) 𝕊 (fstᵛ V) × VRedˢ t' (×ˢ-inj₂ e) 𝕊 (sndᵛ V)
VRedˢ (t ×ˢ t') {Base b}      () 𝕊 V
VRedˢ (t ×ˢ t') {unit}        () 𝕊 V
VRedˢ (t ×ˢ t') {bool}        () 𝕊 V
VRedˢ (t ×ˢ t') {nat}         () 𝕊 V
VRedˢ (t ×ˢ t') {list A}      () 𝕊 V
VRedˢ (t ×ˢ t') {A |+| B}     () 𝕊 V

VRedˢ (t +ˢ t') {A |+| B}     e  𝕊 V =
  VRed⊎ (VRedˢ t (+ˢ-inj₁ e) 𝕊) (VRedˢ t' (+ˢ-inj₂ e) 𝕊) (injᵛ V)
VRedˢ (t +ˢ t') {Base b}      () 𝕊 V
VRedˢ (t +ˢ t') {unit}        () 𝕊 V
VRedˢ (t +ˢ t') {bool}        () 𝕊 V
VRedˢ (t +ˢ t') {nat}         () 𝕊 V
VRedˢ (t +ˢ t') {list A}      () 𝕊 V
VRedˢ (t +ˢ t') {A |×| B}     () 𝕊 V
VRedˢ (t +ˢ t') {empty}       () 𝕊 V
VRedˢ (t +ˢ t') {A ⇒ (B ! ε)} () 𝕊 V
VRedˢ (t +ˢ t') {(A ! ε) ⇛ (B ! ε')} () 𝕊 V
VRedˢ (t +ˢ t') {[ ρ ] A}     () 𝕊 V
VRedˢ (t ×ˢ t') {empty}       () 𝕊 V
VRedˢ (t ×ˢ t') {A ⇒ (B ! ε)} () 𝕊 V
VRedˢ (t ×ˢ t') {(A ! ε) ⇛ (B ! ε')} () 𝕊 V
VRedˢ (t ×ˢ t') {[ ρ ] A}     () 𝕊 V

VRedˢ (Lˢ t) {list A}       e  𝕊 V =
  VRedL (VRedˢ t (Lˢ-inj e) 𝕊) (listᵛ V)
VRedˢ (Lˢ t) {Base b}      () 𝕊 V
VRedˢ (Lˢ t) {unit}        () 𝕊 V
VRedˢ (Lˢ t) {bool}        () 𝕊 V
VRedˢ (Lˢ t) {nat}         () 𝕊 V
VRedˢ (Lˢ t) {A |×| B}     () 𝕊 V
VRedˢ (Lˢ t) {A |+| B}     () 𝕊 V
VRedˢ (Lˢ t) {empty}       () 𝕊 V
VRedˢ (Lˢ t) {A ⇒ (B ! ε)} () 𝕊 V
VRedˢ (Lˢ t) {(A ! ε) ⇛ (B ! ε')} () 𝕊 V
VRedˢ (Lˢ t) {[ ρ ] A}     () 𝕊 V

VRedˢ (t →ˢ t') {A ⇒ (B ! ε)} e  𝕊 V =
  ∀ {𝕊'} → (q : 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊')
  → (W : toCtx 𝕊' ⊢ᵛ⦂ A)
  → VRedˢ t (→ˢ-inj₁ e) 𝕊' W
  → CRed t' (VRedˢ t') (→ˢ-inj₂ e) ε 𝕊' (reach-val q V · W)
VRedˢ (t →ˢ t') {Base b}      () 𝕊 V
VRedˢ (t →ˢ t') {unit}        () 𝕊 V
VRedˢ (t →ˢ t') {bool}        () 𝕊 V
VRedˢ (t →ˢ t') {nat}         () 𝕊 V
VRedˢ (t →ˢ t') {list A}      () 𝕊 V
VRedˢ (t →ˢ t') {A |+| B}     () 𝕊 V
VRedˢ (t →ˢ t') {A |×| B}     () 𝕊 V
VRedˢ (t →ˢ t') {empty}       () 𝕊 V
VRedˢ (t →ˢ t') {(A ! ε) ⇛ (B ! ε')} () 𝕊 V
VRedˢ (t →ˢ t') {[ ρ ] A}     () 𝕊 V

-- the handler and every subsumption of it handle reducible computations

VRedˢ (t ⇛ˢ t') {(A ! ε) ⇛ (B ! ε')} e 𝕊 V =
  ∀ {𝕊'} → (q : 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊')
  → ∀ {A₀ ε₀ B₀ ε₀'} {U : toCtx 𝕊' ⊢ᵛ⦂ (A₀ ! ε₀) ⇛ (B₀ ! ε₀')}
  → (u : Use (reach-val q V) U)
  → (M : toCtx 𝕊' ⊢ᶜ⦂ A₀ ! ε₀)
  → CRed t (VRedˢ t) (use-shape₁ u e) ε₀ 𝕊' M
  → CRed t' (VRedˢ t') (use-shape₂ u e) (ε₀ ·ₑ ε₀') 𝕊' (handle M `with U)
VRedˢ (t ⇛ˢ t') {Base b}      () 𝕊 V
VRedˢ (t ⇛ˢ t') {unit}        () 𝕊 V
VRedˢ (t ⇛ˢ t') {bool}        () 𝕊 V
VRedˢ (t ⇛ˢ t') {nat}         () 𝕊 V
VRedˢ (t ⇛ˢ t') {list A}      () 𝕊 V
VRedˢ (t ⇛ˢ t') {A |+| B}     () 𝕊 V
VRedˢ (t ⇛ˢ t') {A |×| B}     () 𝕊 V
VRedˢ (t ⇛ˢ t') {empty}       () 𝕊 V
VRedˢ (t ⇛ˢ t') {A ⇒ (B ! ε)} () 𝕊 V
VRedˢ (t ⇛ˢ t') {[ ρ ] A}     () 𝕊 V

VRedˢ (□ˢ t) {[ ρ ] A}     e  𝕊 V =
  ∀ {𝕊'} → (r : 𝕊 [ cellᵛ V ]⊑ᶜ 𝕊')
  → VRedˢ t (trans (<:ᵛ-shape (val-subᵛ V)) (□ˢ-inj e)) 𝕊' (lookupᶜ r)
VRedˢ (□ˢ t) {Base b}      () 𝕊 V
VRedˢ (□ˢ t) {unit}        () 𝕊 V
VRedˢ (□ˢ t) {bool}        () 𝕊 V
VRedˢ (□ˢ t) {nat}         () 𝕊 V
VRedˢ (□ˢ t) {list A}      () 𝕊 V
VRedˢ (□ˢ t) {A |+| B}     () 𝕊 V
VRedˢ (□ˢ t) {A |×| B}     () 𝕊 V
VRedˢ (□ˢ t) {empty}       () 𝕊 V
VRedˢ (□ˢ t) {A ⇒ (B ! ε)} () 𝕊 V
VRedˢ (□ˢ t) {(A ! ε) ⇛ (B ! ε')} () 𝕊 V

VRed : (A : VType) → (𝕊 : State []) → toCtx 𝕊 ⊢ᵛ⦂ A → Set
VRed A = VRedˢ (shapeᵛ A) {A} refl

-- Reducible computations at the value predicate `VRed`, the form the
-- fundamental lemma proves. Stated at a shape, so that a subsumption moves the
-- equality index and leaves the predicate alone.

CRedˢ' : (s : Shape) → {A : VType} → shapeᵛ A ≡ s
       → (ε : E) → (𝕊 : State []) → toCtx 𝕊 ⊢ᶜ⦂ A ! ε → Set
CRedˢ' s = CRed s (VRedˢ s)

CRed' : (A : VType) → (ε : E) → (𝕊 : State []) → toCtx 𝕊 ⊢ᶜ⦂ A ! ε → Set
CRed' A = CRedˢ' (shapeᵛ A) {A} refl

-- Two proofs of a shape equality out of the same type carry the predicate
-- across, by UIP on the shared endpoints.

VRedˢ-≡ˢ : ∀ {t t' A} {𝕊 : State []} {V : toCtx 𝕊 ⊢ᵛ⦂ A}
         → {e : shapeᵛ A ≡ t} → {e' : shapeᵛ A ≡ t'}
         → VRedˢ t e 𝕊 V → VRedˢ t' e' 𝕊 V
VRedˢ-≡ˢ {e = refl} {e' = refl} p = p

VRedˢ-≡ᵛ : ∀ {t A} {𝕊 : State []} {e : shapeᵛ A ≡ t} {V V' : toCtx 𝕊 ⊢ᵛ⦂ A}
         → V ≡ V' → VRedˢ t e 𝕊 V → VRedˢ t e 𝕊 V'
VRedˢ-≡ᵛ refl p = p

CRedˢ'-≡ˢ : ∀ {t t' A ε} {𝕊 : State []} {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
          → {e : shapeᵛ A ≡ t} → {e' : shapeᵛ A ≡ t'}
          → CRedˢ' t e ε 𝕊 M → CRedˢ' t' e' ε 𝕊 M
CRedˢ'-≡ˢ {e = refl} {e' = refl} p = p

-- Every cell of the state holds a value that is reducible at any later state
-- at which it is readable.

SRed : State [] → Set
SRed 𝕊 = ∀ {A ρ σ} {𝕊' : State []} → (c : [ ρ ] A ∈[ σ ] toCtx 𝕊)
       → (r : 𝕊 [ c ]⊑ᶜ 𝕊')
       → VRed A 𝕊' (lookupᶜ r)

-- A step in front of a reducible computation reaches the same whnf by a
-- longer run. `CRed` carries runs, so `_▸_` leaves the grade and the value
-- type free; only the stored shape equality is kept.

CRed-expand : ∀ {s} {P : VPred s} {A A₀ ε ε₀} {𝕊 𝕊₀ : State []}
            → {e : shapeᵛ A ≡ s} → {e₀ : shapeᵛ A₀ ≡ s}
            → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → {M₀ : toCtx 𝕊₀ ⊢ᶜ⦂ A₀ ! ε₀}
            → ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊₀ ∣ M₀ ⟩
            → CRed s P e₀ ε₀ 𝕊₀ M₀
            -------------------------
            → CRed s P e ε 𝕊 M

CRed-expand r (cred-ret e₀ rs pV)   = cred-ret e₀ (r ▸ rs) pV
CRed-expand r (cred-op e₀ rs pW pk) = cred-op e₀ (r ▸ rs) pW pk

-- A whole run in front of a reducible computation, and transporting one along an
-- equality of effects (which `SEQ-OP`'s reduct carries).

CRed-expand* : ∀ {s} {P : VPred s} {A A₀ ε ε₀} {𝕊 𝕊₀ : State []}
             → {e : shapeᵛ A ≡ s} → {e₀ : shapeᵛ A₀ ≡ s}
             → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → {M₀ : toCtx 𝕊₀ ⊢ᶜ⦂ A₀ ! ε₀}
             → ⟨ 𝕊 ∣ M ⟩ ⟶* ⟨ 𝕊₀ ∣ M₀ ⟩
             → CRed s P e₀ ε₀ 𝕊₀ M₀
             -------------------------
             → CRed s P e ε 𝕊 M

CRed-expand* {s = s} {P = P} {ε = ε} {𝕊 = 𝕊} {M = M} done p =
  subst (λ z → CRed s P z ε 𝕊 M) uip p
CRed-expand* {e = e} (r ▸ rs) p =
  CRed-expand r
    (CRed-expand* {e = trans (<:ᵛ-shape (step-refines-type r)) e} rs p)

CRed-ε-subst : ∀ {s} {P : VPred s} {A ε ε'} {e : shapeᵛ A ≡ s} {𝕊 : State []}
             → (eε : ε ≡ ε') → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
             → CRed s P e ε 𝕊 M → CRed s P e ε' 𝕊 (ε-subst eε M)
CRed-ε-subst refl p = p

-- A sub-effected computation is its own reduct, one `SUB` step on.

CRed-coerce : ∀ {s} {P : VPred s} {A ε ε'} {e : shapeᵛ A ≡ s} {𝕊 : State []}
            → (q : ε ≾ₑ ε') → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
            → CRed s P e ε 𝕊 M → CRed s P e ε' 𝕊 (coerce q M)
CRed-coerce q = CRed-expand SUB

-- Reducibility is monotone in the subtyping order. Both halves are stated at a
-- fixed skeleton, the subtyping witness moving the equality index alone. The
-- value half recurses on the witness; at an arrow `SUB-APP` splits the witness
-- across the application, the codomain half becoming the step's refinement. At
-- a box both sides quantify over the same reads of the same cell.

VRedˢ-sub : ∀ {s A A'} {e : shapeᵛ A ≡ s} {e' : shapeᵛ A' ≡ s} {𝕊 : State []}
          → (p : A <:ᵛ A') → (V : toCtx 𝕊 ⊢ᵛ⦂ A)
          → VRedˢ s e 𝕊 V → VRedˢ s e' 𝕊 (subV V p)

VRedˢ-sub {e' = refl} (Baseₛ refl) V pV         = tt
VRedˢ-sub {e' = refl} unitₛ        V pV         = tt
VRedˢ-sub {e' = refl} boolₛ        V pV         = tt
VRedˢ-sub {e' = refl} natₛ         V pV         = tt
VRedˢ-sub {e' = refl} emptyₛ       V pV         = tt
VRedˢ-sub {e' = refl} (p |×|ₛ p')  V (pV , pV') =
  VRedˢ-sub p (fstᵛ V) pV , VRedˢ-sub p' (sndᵛ V) pV'
VRedˢ-sub {A' = A₂ |+| B₂} {e = e} {e' = refl} {𝕊 = 𝕊} (p |+|ₛ p') V pV =
  sub-inj pV
  where
    sub-inj : ∀ {s}
            → VRed⊎ (VRedˢ (shapeᵛ A₂) (+ˢ-inj₁ e) 𝕊) (VRedˢ (shapeᵛ B₂) (+ˢ-inj₂ e) 𝕊) s
            → VRed⊎ (VRedˢ (shapeᵛ A₂) refl 𝕊) (VRedˢ (shapeᵛ B₂) refl 𝕊) (sub⊎ p p' s)
    sub-inj (red-inl pW) = red-inl (VRedˢ-sub p _ pW)
    sub-inj (red-inr pW) = red-inr (VRedˢ-sub p' _ pW)
VRedˢ-sub {e' = refl} (listₛ p) V pV =
  VRedL-sub p (λ W → VRedˢ-sub p W) pV
VRedˢ-sub {e' = refl} (p ⇒ₛ (p' !ₛ q)) V f      =
  λ q₀ W pW → CRed-expand SUB-APP (f q₀ (subV W p) (VRedˢ-sub p W pW))
VRedˢ-sub {e' = refl} ([ _ ]ₛ p)   V f          = λ r → VRedˢ-≡ˢ (f r)
VRedˢ-sub {e' = refl} (p@(_ !ₛ _) ⇛ₛ p'@(_ !ₛ _)) V f = λ where
  q₀ use-id M pM →
    CRedˢ'-≡ˢ (f q₀ (use-sub (p ⇛ₛ p')) M (CRedˢ'-≡ˢ pM))
  q₀ (use-sub w) M pM →
    CRed-expand SUB-HANDLE-TRANS
      (f q₀ (use-sub (<:ᵛ-trans (p ⇛ₛ p') w)) M (CRedˢ'-≡ˢ pM))

VRed-sub : ∀ {A A'} {𝕊 : State []} → (p : A <:ᵛ A')
         → (V : toCtx 𝕊 ⊢ᵛ⦂ A) → VRed A 𝕊 V → VRed A' 𝕊 (subV V p)

VRed-sub p V pV = VRedˢ-sub {e = <:ᵛ-shape p} p V (VRedˢ-≡ˢ pV)

-- A run refines the value type one subsumption at a time, and `spine` applies
-- them in order; reducibility travels along it.

VRed-spine : ∀ {A B ε ε'} {cf : Config (A ! ε)} {cf' : Config (B ! ε')}
           → (rs : cf ⟶* cf') → {𝕊 : State []} → (V : toCtx 𝕊 ⊢ᵛ⦂ B)
           → VRed B 𝕊 V → VRed A 𝕊 (spine rs V)

VRed-spine done     V pV = pV
VRed-spine (r ▸ rs) V pV =
  VRed-sub (step-refines-type r) (spine rs V) (VRed-spine rs V pV)

-- A subsumed computation is its own reduct, one `SUB` step on.

CRed-sub : ∀ {s A A' ε ε₀} {e : shapeᵛ A ≡ s} {e' : shapeᵛ A' ≡ s} {𝕊 : State []}
         → (p : A <:ᵛ A') → (q : ε ≾ₑ ε₀)
         → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
         → CRedˢ' s e ε 𝕊 M → CRedˢ' s e' ε₀ 𝕊 (subC M (p !ₛ q))

CRed-sub p q = CRed-expand SUB

CRed'-sub : ∀ {A A' ε ε₀} {𝕊 : State []} → (p : A <:ᵛ A') → (q : ε ≾ₑ ε₀)
          → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
          → CRed' A ε 𝕊 M → CRed' A' ε₀ 𝕊 (subC M (p !ₛ q))

CRed'-sub p q pM = CRed-sub {e = <:ᵛ-shape p} p q (CRedˢ'-≡ˢ pM)

-- The empty store: `toCtx ∅` has no variables.

SRed-∅ : SRed ∅
SRed-∅ c r = ⊥-elim (not-in-empty-ctx c)

-- A boolean over a state context runs to one of the two constants: a variable
-- is ruled out by `bool-not-in-toCtx`, and a subsumption is dropped by
-- `SUB-IF`.

bool-canonical : ∀ {𝕊 : State []} → (V : toCtx 𝕊 ⊢ᵛ⦂ bool)
               → (∀ {A ε} {M N : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
                    → ⟨ 𝕊 ∣ if V `then M `else N ⟩ ⟶* ⟨ 𝕊 ∣ M ⟩)
               ⊎ (∀ {A ε} {M N : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
                    → ⟨ 𝕊 ∣ if V `then M `else N ⟩ ⟶* ⟨ 𝕊 ∣ N ⟩)
bool-canonical (var f x)      = ⊥-elim (bool-not-in-toCtx x)
bool-canonical true           = inj₁ (IF-TRUE ▸ done)
bool-canonical false          = inj₂ (IF-FALSE ▸ done)
bool-canonical (subV V boolₛ) with bool-canonical V
... | inj₁ rs = inj₁ (SUB-IF ▸ rs)
... | inj₂ rs = inj₂ (SUB-IF ▸ rs)

-- A natural number over a state context runs to the zero branch or to the
-- successor branch at a predecessor: a variable is ruled out by
-- `nat-not-in-toCtx`, and a subsumption is dropped by `SUB-MATCHℕ`.

nat-canonical : ∀ {𝕊 : State []} → (V : toCtx 𝕊 ⊢ᵛ⦂ nat)
              → (∀ {A ε} {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} {N : toCtx 𝕊 ∷ nat ⊢ᶜ⦂ A ! ε}
                   → ⟨ 𝕊 ∣ matchℕ V `zero M `succ N ⟩ ⟶* ⟨ 𝕊 ∣ M ⟩)
              ⊎ Σ[ W ∈ toCtx 𝕊 ⊢ᵛ⦂ nat ]
                  (∀ {A ε} {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} {N : toCtx 𝕊 ∷ nat ⊢ᶜ⦂ A ! ε}
                     → ⟨ 𝕊 ∣ matchℕ V `zero M `succ N ⟩ ⟶* ⟨ 𝕊 ∣ N [ split-[] ↦ W ]c ⟩)
nat-canonical (var f x)     = ⊥-elim (nat-not-in-toCtx x)
nat-canonical zero          = inj₁ (MATCHℕ-ZERO ▸ done)
nat-canonical (succ V)      = inj₂ (V , MATCHℕ-SUCC ▸ done)
nat-canonical (subV V natₛ) with nat-canonical V
... | inj₁ rs       = inj₁ (SUB-MATCHℕ ▸ rs)
... | inj₂ (W , rs) = inj₂ (W , SUB-MATCHℕ ▸ rs)

-- An eternal type is built from base, unit, boolean, natural-number and empty
-- types, products, sums and lists, so `VRed` asks nothing of a value of
-- eternal type beyond its injections and its decomposition.

-- A predicate that holds of every element holds of every decomposition.

VRedL-all : ∀ {𝕊 : State []} {A} {P : toCtx 𝕊 ⊢ᵛ⦂ A → Set}
          → (∀ W → P W) → (V : toCtx 𝕊 ⊢ᵛ⦂ list A) → VRedL P (listᵛ V)
VRedL-all h (var _ x)            = ⊥-elim (list-not-in-toCtx x)
VRedL-all h nil                  = red-nil
VRedL-all h (cons W L)           = red-cons (h W) (VRedL-all h L)
VRedL-all h (subV V (listₛ p))   =
  VRedL-sub p (λ W pW → pW) (VRedL-all (λ W → h (subV W p)) V)

VRed-eternal : ∀ {A} {𝕊 : State []} → Et A → (V : toCtx 𝕊 ⊢ᵛ⦂ A) → VRed A 𝕊 V

VRed-eternal (Baseₑ _)        V = tt
VRed-eternal unitₑ            V = tt
VRed-eternal boolₑ            V = tt
VRed-eternal natₑ             V = tt
VRed-eternal emptyₑ           V = tt
VRed-eternal (et₁ |×|ₑ et₂)   V =
  VRed-eternal et₁ (fstᵛ V) , VRed-eternal et₂ (sndᵛ V)
VRed-eternal (et₁ |+|ₑ et₂)   V = eternal-inj (injᵛ V)
  where
    eternal-inj : ∀ s → VRed⊎ (VRed _ _) (VRed _ _) s
    eternal-inj (inj₁ W) = red-inl (VRed-eternal et₁ W)
    eternal-inj (inj₂ W) = red-inr (VRed-eternal et₂ W)
VRed-eternal (listₑ et)       V = VRedL-all (VRed-eternal et) V

VRed-≡ᵛ : ∀ {𝕊 : State []} → (A : VType) → {V V' : toCtx 𝕊 ⊢ᵛ⦂ A}
        → V ≡ V' → VRed A 𝕊 V → VRed A 𝕊 V'

VRed-≡ᵛ A refl p = p

-- Reading a cell after a reach is reading it before: the payload is the same
-- value, so what holds of it transports. An induction on the value: the spine
-- passes it on, and the variable clause is where the reach is absorbed.

reach-read-val : ∀ {t A ρ} {𝕊 𝕊' : State []} → (q : 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊')
               → (V : toCtx 𝕊 ⊢ᵛ⦂ [ ρ ] A)
               → (e : shapeᵛ (val-typeᵛ V) ≡ t)
               → (e' : shapeᵛ (val-typeᵛ (reach-val q V)) ≡ t)
               → (∀ {𝕊₂ : State []} → (r₀ : 𝕊 [ cellᵛ V ]⊑ᶜ 𝕊₂)
                    → VRedˢ t e 𝕊₂ (lookupᶜ r₀))
               -------------------------------------------------------------
               → ∀ {𝕊₂ : State []} → (r : 𝕊' [ cellᵛ (reach-val q V) ]⊑ᶜ 𝕊₂)
               → VRedˢ t e' 𝕊₂ (lookupᶜ r)

reach-read-val {ρ = ρ} q (var _ x) e e' h {𝕊₂} (read ee rel) =
  VRedˢ-≡ˢ (VRedˢ-≡ᵛ (lookup-body-≡ 𝕊₂ cellEq rel₁ rel)
                     (h (read (≤ₛ-trans (ext q) ee) rel₁)))
  where
    cellEq = trans (≤ₛ-embed-∘ (ext q) ee x)
                   (sym (cong (λ z → ≤ₛ-embed ee (proj₂ z))
                              (reach-renᵘ-img q x)))
    rel₁ = subst (_≾ᵣ ρ) (sym (cong proj₁ cellEq)) rel

reach-read-val q (subV V ([ _ ]ₛ _)) e e' h r = reach-read-val q V e e' h r

VRedˢ-reach : ∀ {t A} {𝕊 𝕊' : State []} → (q : 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊')
            → (e : shapeᵛ A ≡ t) → (V : toCtx 𝕊 ⊢ᵛ⦂ A)
            → VRedˢ t e 𝕊 V → VRedˢ t e 𝕊' (reach-val q V)

VRedˢ-reach {⋆ˢ} q e V p = tt

VRedˢ-reach {t ×ˢ t'} {A |×| B}     q e  V (p₁ , p₂) =
    VRedˢ-≡ᵛ (sym (fstᵛ-ren (reach-renᵘ q) V))
             (VRedˢ-reach q (×ˢ-inj₁ e) (fstᵛ V) p₁)
  , VRedˢ-≡ᵛ (sym (sndᵛ-ren (reach-renᵘ q) V))
             (VRedˢ-reach q (×ˢ-inj₂ e) (sndᵛ V) p₂)
VRedˢ-reach {t ×ˢ t'} {Base b}      q () V p
VRedˢ-reach {t ×ˢ t'} {unit}        q () V p
VRedˢ-reach {t ×ˢ t'} {bool}        q () V p
VRedˢ-reach {t ×ˢ t'} {nat}         q () V p
VRedˢ-reach {t ×ˢ t'} {list A}      q () V p
VRedˢ-reach {t ×ˢ t'} {A |+| B}     q () V p
VRedˢ-reach {t ×ˢ t'} {empty}       q () V p
VRedˢ-reach {t ×ˢ t'} {A ⇒ (B ! ε)} q () V p
VRedˢ-reach {t ×ˢ t'} {(A ! ε) ⇛ (B ! ε')} q () V p
VRedˢ-reach {t ×ˢ t'} {[ ρ ] A}     q () V p

VRedˢ-reach {t +ˢ t'} {A |+| B}     q e  V p =
  subst (VRed⊎ (VRedˢ t (+ˢ-inj₁ e) _) (VRedˢ t' (+ˢ-inj₂ e) _))
        (sym (injᵛ-ren (reach-renᵘ q) V)) (reach-inj p)
  where
    reach-inj : ∀ {s} → VRed⊎ (VRedˢ t (+ˢ-inj₁ e) _) (VRedˢ t' (+ˢ-inj₂ e) _) s
              → VRed⊎ (VRedˢ t (+ˢ-inj₁ e) _) (VRedˢ t' (+ˢ-inj₂ e) _)
                  (ren⊎ (reach-renᵘ q) s)
    reach-inj (red-inl pW) = red-inl (VRedˢ-reach q (+ˢ-inj₁ e) _ pW)
    reach-inj (red-inr pW) = red-inr (VRedˢ-reach q (+ˢ-inj₂ e) _ pW)
VRedˢ-reach {t +ˢ t'} {Base b}      q () V p
VRedˢ-reach {t +ˢ t'} {unit}        q () V p
VRedˢ-reach {t +ˢ t'} {bool}        q () V p
VRedˢ-reach {t +ˢ t'} {nat}         q () V p
VRedˢ-reach {t +ˢ t'} {list A}      q () V p
VRedˢ-reach {t +ˢ t'} {A |×| B}     q () V p
VRedˢ-reach {t +ˢ t'} {empty}       q () V p
VRedˢ-reach {t +ˢ t'} {A ⇒ (B ! ε)} q () V p
VRedˢ-reach {t +ˢ t'} {(A ! ε) ⇛ (B ! ε')} q () V p
VRedˢ-reach {t +ˢ t'} {[ ρ ] A}     q () V p

VRedˢ-reach {Lˢ t} {list A}       q e  V p =
  subst (VRedL (VRedˢ t (Lˢ-inj e) _)) (sym (listᵛ-ren (reach-renᵘ q) V))
        (reach-list p)
  where
    reach-list : ∀ {l} → VRedL (VRedˢ t (Lˢ-inj e) _) l
               → VRedL (VRedˢ t (Lˢ-inj e) _) (renL (reach-renᵘ q) l)
    reach-list red-nil = red-nil
    reach-list (red-cons {W} {L} pW pL) =
      red-cons (VRedˢ-reach q (Lˢ-inj e) W pW)
               (subst (VRedL (VRedˢ t (Lˢ-inj e) _)) (sym (listᵛ-ren (reach-renᵘ q) L))
                      (reach-list pL))
VRedˢ-reach {Lˢ t} {Base b}      q () V p
VRedˢ-reach {Lˢ t} {unit}        q () V p
VRedˢ-reach {Lˢ t} {bool}        q () V p
VRedˢ-reach {Lˢ t} {nat}         q () V p
VRedˢ-reach {Lˢ t} {A |×| B}     q () V p
VRedˢ-reach {Lˢ t} {A |+| B}     q () V p
VRedˢ-reach {Lˢ t} {empty}       q () V p
VRedˢ-reach {Lˢ t} {A ⇒ (B ! ε)} q () V p
VRedˢ-reach {Lˢ t} {(A ! ε) ⇛ (B ! ε')} q () V p
VRedˢ-reach {Lˢ t} {[ ρ ] A}     q () V p

VRedˢ-reach {t →ˢ t'} {A ⇒ (B ! ε)} q₀ e  V f = λ q' W pW →
  subst (λ z → CRed t' (VRedˢ t') (→ˢ-inj₂ e) ε _ (z · W))
        (trans (V-rename-≡ (reach-renᵘ-∘ q' q₀) V)
               (V-rename-∘ (reach-renᵘ q₀) (reach-renᵘ q') V))
        (f (reach-∘ q' q₀) W pW)
VRedˢ-reach {t →ˢ t'} {Base b}      q () V f
VRedˢ-reach {t →ˢ t'} {unit}        q () V f
VRedˢ-reach {t →ˢ t'} {bool}        q () V f
VRedˢ-reach {t →ˢ t'} {nat}         q () V f
VRedˢ-reach {t →ˢ t'} {list A}      q () V f
VRedˢ-reach {t →ˢ t'} {A |+| B}     q () V f
VRedˢ-reach {t →ˢ t'} {A |×| B}     q () V f
VRedˢ-reach {t →ˢ t'} {empty}       q () V f
VRedˢ-reach {t →ˢ t'} {(A ! ε) ⇛ (B ! ε')} q () V f
VRedˢ-reach {t →ˢ t'} {[ ρ ] A}     q () V f

VRedˢ-reach {t ⇛ˢ t'} {(A ! ε) ⇛ (B ! ε')} q₀ e V f = λ q' u M pM →
  CRedˢ'-≡ˢ (f (reach-∘ q' q₀) (subst (λ z → Use z _) (sym eq) u) M (CRedˢ'-≡ˢ pM))
  where
    eq : ∀ {𝕊''} {q' : _ ⊑ₛ[ 𝟏ᵣ ] 𝕊''}
       → reach-val (reach-∘ q' q₀) V ≡ reach-val q' (reach-val q₀ V)
    eq {q' = q'} = trans (V-rename-≡ (reach-renᵘ-∘ q' q₀) V)
                         (V-rename-∘ (reach-renᵘ q₀) (reach-renᵘ q') V)
VRedˢ-reach {t ⇛ˢ t'} {Base b}      q () V f
VRedˢ-reach {t ⇛ˢ t'} {unit}        q () V f
VRedˢ-reach {t ⇛ˢ t'} {bool}        q () V f
VRedˢ-reach {t ⇛ˢ t'} {nat}         q () V f
VRedˢ-reach {t ⇛ˢ t'} {list A}      q () V f
VRedˢ-reach {t ⇛ˢ t'} {A |+| B}     q () V f
VRedˢ-reach {t ⇛ˢ t'} {A |×| B}     q () V f
VRedˢ-reach {t ⇛ˢ t'} {empty}       q () V f
VRedˢ-reach {t ⇛ˢ t'} {A ⇒ (B ! ε)} q () V f
VRedˢ-reach {t ⇛ˢ t'} {[ ρ ] A}     q () V f

VRedˢ-reach {□ˢ t} {[ ρ ] A}     q e  V f = reach-read-val q V _ _ f
VRedˢ-reach {□ˢ t} {Base b}      q () V f
VRedˢ-reach {□ˢ t} {unit}        q () V f
VRedˢ-reach {□ˢ t} {bool}        q () V f
VRedˢ-reach {□ˢ t} {nat}         q () V f
VRedˢ-reach {□ˢ t} {list A}      q () V f
VRedˢ-reach {□ˢ t} {A |+| B}     q () V f
VRedˢ-reach {□ˢ t} {A |×| B}     q () V f
VRedˢ-reach {□ˢ t} {empty}       q () V f
VRedˢ-reach {□ˢ t} {A ⇒ (B ! ε)} q () V f
VRedˢ-reach {□ˢ t} {(A ! ε) ⇛ (B ! ε')} q () V f

VRed-reach : ∀ {A 𝕊 𝕊'} → (q : 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊') → (V : toCtx 𝕊 ⊢ᵛ⦂ A)
           → VRed A 𝕊 V → VRed A 𝕊' (reach-val q V)

VRed-reach q V p = VRedˢ-reach q refl V p

-- `VRedᵍ` is `VRed` restricted to the ground types, whose skeletons have no
-- arrows, so the two predicates coincide clause for clause. Two recursions on
-- the ground type, with the value's own type left free, since a box's read is at
-- the cell's declared type, not the one named.

VRedˢ→VRedᵍˢ : (G : GType) → ∀ {A} {𝕊 : State []}
             → (e : shapeᵛ A ≡ shapeᵛ ⌜ G ⌝ᵍ)
             → (V : toCtx 𝕊 ⊢ᵛ⦂ A)
             → VRedˢ (shapeᵛ ⌜ G ⌝ᵍ) e 𝕊 V
             → VRedᵍˢ (shapeᵛ ⌜ G ⌝ᵍ) e 𝕊 V

VRedˢ→VRedᵍˢ (Base b) e V p = tt
VRedˢ→VRedᵍˢ unit     e V p = tt
VRedˢ→VRedᵍˢ bool     e V p = tt
VRedˢ→VRedᵍˢ nat      e V p = tt
VRedˢ→VRedᵍˢ empty    e V p = tt

VRedˢ→VRedᵍˢ (G₁ |+|ᵍ G₂) {A |+| B}     e  V p =
  VRed⊎-map (λ W → VRedˢ→VRedᵍˢ G₁ (+ˢ-inj₁ e) W)
            (λ W → VRedˢ→VRedᵍˢ G₂ (+ˢ-inj₂ e) W) p
VRedˢ→VRedᵍˢ (G₁ |+|ᵍ G₂) {Base b}      () V p
VRedˢ→VRedᵍˢ (G₁ |+|ᵍ G₂) {unit}        () V p
VRedˢ→VRedᵍˢ (G₁ |+|ᵍ G₂) {bool}        () V p
VRedˢ→VRedᵍˢ (G₁ |+|ᵍ G₂) {nat}         () V p
VRedˢ→VRedᵍˢ (G₁ |+|ᵍ G₂) {list A}      () V p
VRedˢ→VRedᵍˢ (G₁ |+|ᵍ G₂) {A |×| B}     () V p
VRedˢ→VRedᵍˢ (G₁ |+|ᵍ G₂) {empty}       () V p
VRedˢ→VRedᵍˢ (G₁ |+|ᵍ G₂) {A ⇒ (B ! ε)} () V p
VRedˢ→VRedᵍˢ (G₁ |+|ᵍ G₂) {(A ! ε) ⇛ (B ! ε')} () V p
VRedˢ→VRedᵍˢ (G₁ |+|ᵍ G₂) {[ ρ ] A}     () V p

VRedˢ→VRedᵍˢ (listᵍ G) {list A}        e  V p =
  VRedL-map (λ W → VRedˢ→VRedᵍˢ G (Lˢ-inj e) W) p
VRedˢ→VRedᵍˢ (listᵍ G) {Base b}        () V p
VRedˢ→VRedᵍˢ (listᵍ G) {unit}          () V p
VRedˢ→VRedᵍˢ (listᵍ G) {bool}          () V p
VRedˢ→VRedᵍˢ (listᵍ G) {nat}           () V p
VRedˢ→VRedᵍˢ (listᵍ G) {A |×| B}       () V p
VRedˢ→VRedᵍˢ (listᵍ G) {A |+| B}       () V p
VRedˢ→VRedᵍˢ (listᵍ G) {empty}         () V p
VRedˢ→VRedᵍˢ (listᵍ G) {A ⇒ (B ! ε)}   () V p
VRedˢ→VRedᵍˢ (listᵍ G) {(A ! ε) ⇛ (B ! ε')} () V p
VRedˢ→VRedᵍˢ (listᵍ G) {[ ρ ] A}       () V p

VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {A |×| B}     e  V (p₁ , p₂) =
    VRedˢ→VRedᵍˢ G₁ (×ˢ-inj₁ e) (fstᵛ V) p₁
  , VRedˢ→VRedᵍˢ G₂ (×ˢ-inj₂ e) (sndᵛ V) p₂
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {Base b}      () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {unit}        () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {bool}        () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {nat}         () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {list A}      () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {A |+| B}     () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {empty}       () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {A ⇒ (B ! ε)} () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {(A ! ε) ⇛ (B ! ε')} () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {[ ρ ] A}     () V p

VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {[ ρ ] A}     e  V p =
  λ r → VRedˢ→VRedᵍˢ G _ (lookupᶜ r) (p r)
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {Base b}      () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {unit}        () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {bool}        () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {nat}         () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {list A}      () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {A |+| B}     () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {A |×| B}     () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {empty}       () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {A ⇒ (B ! ε)} () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {(A ! ε) ⇛ (B ! ε')} () V p

VRedᵍˢ→VRedˢ : (G : GType) → ∀ {A} {𝕊 : State []}
             → (e : shapeᵛ A ≡ shapeᵛ ⌜ G ⌝ᵍ)
             → (V : toCtx 𝕊 ⊢ᵛ⦂ A)
             → VRedᵍˢ (shapeᵛ ⌜ G ⌝ᵍ) e 𝕊 V
             → VRedˢ (shapeᵛ ⌜ G ⌝ᵍ) e 𝕊 V

VRedᵍˢ→VRedˢ (Base b) e V p = tt
VRedᵍˢ→VRedˢ unit     e V p = tt
VRedᵍˢ→VRedˢ bool     e V p = tt
VRedᵍˢ→VRedˢ nat      e V p = tt
VRedᵍˢ→VRedˢ empty    e V p = tt

VRedᵍˢ→VRedˢ (G₁ |+|ᵍ G₂) {A |+| B}     e  V p =
  VRed⊎-map (λ W → VRedᵍˢ→VRedˢ G₁ (+ˢ-inj₁ e) W)
            (λ W → VRedᵍˢ→VRedˢ G₂ (+ˢ-inj₂ e) W) p
VRedᵍˢ→VRedˢ (G₁ |+|ᵍ G₂) {Base b}      () V p
VRedᵍˢ→VRedˢ (G₁ |+|ᵍ G₂) {unit}        () V p
VRedᵍˢ→VRedˢ (G₁ |+|ᵍ G₂) {bool}        () V p
VRedᵍˢ→VRedˢ (G₁ |+|ᵍ G₂) {nat}         () V p
VRedᵍˢ→VRedˢ (G₁ |+|ᵍ G₂) {list A}      () V p
VRedᵍˢ→VRedˢ (G₁ |+|ᵍ G₂) {A |×| B}     () V p
VRedᵍˢ→VRedˢ (G₁ |+|ᵍ G₂) {empty}       () V p
VRedᵍˢ→VRedˢ (G₁ |+|ᵍ G₂) {A ⇒ (B ! ε)} () V p
VRedᵍˢ→VRedˢ (G₁ |+|ᵍ G₂) {(A ! ε) ⇛ (B ! ε')} () V p
VRedᵍˢ→VRedˢ (G₁ |+|ᵍ G₂) {[ ρ ] A}     () V p

VRedᵍˢ→VRedˢ (listᵍ G) {list A}        e  V p =
  VRedL-map (λ W → VRedᵍˢ→VRedˢ G (Lˢ-inj e) W) p
VRedᵍˢ→VRedˢ (listᵍ G) {Base b}        () V p
VRedᵍˢ→VRedˢ (listᵍ G) {unit}          () V p
VRedᵍˢ→VRedˢ (listᵍ G) {bool}          () V p
VRedᵍˢ→VRedˢ (listᵍ G) {nat}           () V p
VRedᵍˢ→VRedˢ (listᵍ G) {A |×| B}       () V p
VRedᵍˢ→VRedˢ (listᵍ G) {A |+| B}       () V p
VRedᵍˢ→VRedˢ (listᵍ G) {empty}         () V p
VRedᵍˢ→VRedˢ (listᵍ G) {A ⇒ (B ! ε)}   () V p
VRedᵍˢ→VRedˢ (listᵍ G) {(A ! ε) ⇛ (B ! ε')} () V p
VRedᵍˢ→VRedˢ (listᵍ G) {[ ρ ] A}       () V p

VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {A |×| B}     e  V (p₁ , p₂) =
    VRedᵍˢ→VRedˢ G₁ (×ˢ-inj₁ e) (fstᵛ V) p₁
  , VRedᵍˢ→VRedˢ G₂ (×ˢ-inj₂ e) (sndᵛ V) p₂
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {Base b}      () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {unit}        () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {bool}        () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {nat}         () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {list A}      () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {A |+| B}     () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {empty}       () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {A ⇒ (B ! ε)} () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {(A ! ε) ⇛ (B ! ε')} () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {[ ρ ] A}     () V p

VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {[ ρ ] A}     e  V p =
  λ r → VRedᵍˢ→VRedˢ G _ (lookupᶜ r) (p r)
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {Base b}      () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {unit}        () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {bool}        () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {nat}         () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {list A}      () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {A |+| B}     () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {A |×| B}     () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {empty}       () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {A ⇒ (B ! ε)} () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {(A ! ε) ⇛ (B ! ε')} () V p

VRed→VRedᵍ : (G : GType) → {𝕊 : State []} → (V : toCtx 𝕊 ⊢ᵛ⦂ ⌜ G ⌝ᵍ)
           → VRed ⌜ G ⌝ᵍ 𝕊 V → VRedᵍ G 𝕊 V

VRed→VRedᵍ G V p = VRedˢ→VRedᵍˢ G refl V p

VRedᵍ→VRed : (G : GType) → {𝕊 : State []} → (V : toCtx 𝕊 ⊢ᵛ⦂ ⌜ G ⌝ᵍ)
           → VRedᵍ G 𝕊 V → VRed ⌜ G ⌝ᵍ 𝕊 V

VRedᵍ→VRed G V p = VRedᵍˢ→VRedˢ G refl V p

-- Ground reducibility is insensitive to the equivalence, as `VRed-≡ᵛ` is.

VRedᵍ-≡ᵛ : ∀ {𝕊 : State []} → (G : GType) → {V V' : toCtx 𝕊 ⊢ᵛ⦂ ⌜ G ⌝ᵍ}
         → V ≡ V' → VRedᵍ G 𝕊 V → VRedᵍ G 𝕊 V'

VRedᵍ-≡ᵛ G refl p = p

-- Reducibility is insensitive to the term equivalence.

CRed-≡ᶜ : ∀ {A ε} {𝕊 : State []} {M M' : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
        → M ≡ M' → CRed' A ε 𝕊 M → CRed' A ε 𝕊 M'
CRed-≡ᶜ refl p = p

-- Handling is `Termination.Handle`, above `Environment`: as sequencing, plus a
-- clause premise, and needing `sub-wk-C` for the same reason.

-- The freshly allocated cell is reducible: a reach out of `𝕊 ∷ₛ V` at `ρ`
-- is one out of `𝕊`, and reading the cell back returns the stored value.

SRed-fresh : ∀ {A ρ} {𝕊 : State []} → (V : ([] ++ᶜ toCtx 𝕊 ⟨ ρ ⟩) ⊢ᵛ⦂ A)
           → (∀ {𝕊'} → (q : 𝕊 ⊑ₛ[ ρ ] 𝕊')
                → VRed A 𝕊' (V-rename (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q) V))
           → (f : ¬ Et ([ ρ ] A) → 𝟏ᵣ ≾ᵣ 𝟏ᵣ)
           ------------------------------------------
           → VRed ([ ρ ] A) (𝕊 ∷ₛ V) (var f Hd)

SRed-fresh {A} {ρ} {𝕊} V pV f {𝕊'} r =
  VRedˢ-≡ˢ (VRed-≡ᵛ A (sym (alloc-lookup-≡ V (extᶜ r) (ready r) q₀ refl))
                      (pV q₀))
  where
    e   = extᶜ r
    rel = ready r
    -- the allocation accumulates nothing, so the cell's readability at `𝕊'`
    -- is the bound the reach back to `𝕊` needs
    q₀ : 𝕊 ⊑ₛ[ ρ ] 𝕊'
    q₀ = reach (≤ₛ-trans (≤ₛ-res ≤ₛ-refl) e)
               (≾ᵣ-trans
                 (≃ᵣ⇒≾ᵣ
                   (≃ᵣ-trans (κₛ-trans (≤ₛ-res ≤ₛ-refl) e) (≃ᵣ-sym (≤ₛ-embed-grade e (Hd {Γ = toCtx 𝕊})))))
                 rel)

-- Every variable of a state context is of box type, so at the other
-- types there is nothing to show. At a box type a usable variable is
-- reducible via the store read at the states its own box grade allows.

SRed-var : ∀ {A ρ} {𝕊 : State []} → SRed 𝕊
         → (x : A ∈[ ρ ] toCtx 𝕊) → (f : ¬ Et A → ρ ≾ᵣ 𝟏ᵣ)
         --------------------------------------------------------
         → VRed A 𝕊 (var f x)

SRed-var {Base b}    pSt x f = tt
SRed-var {unit}      pSt x f = tt
SRed-var {bool}      pSt x f = tt
SRed-var {nat}       pSt x f = tt
SRed-var {empty}     pSt x f = tt
SRed-var {A₁ |×| A₂} pSt x f = ⊥-elim (⦉⦊-not-in-toCtx x)
SRed-var {A₁ |+| A₂} pSt x f = ⊥-elim (|+|-not-in-toCtx x)
SRed-var {list A₁}   pSt x f = ⊥-elim (list-not-in-toCtx x)
SRed-var {A₁ ⇒ C}    pSt x f = ⊥-elim (⇒-not-in-toCtx x)
SRed-var {C ⇛ D}     pSt x f = ⊥-elim (⇛-not-in-toCtx x)

SRed-var {[ ρ ] A} pSt x f r = VRedˢ-≡ˢ (pSt x r)
