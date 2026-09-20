------------------------------------------------------------------------
-- The logical relation: reducible values, computations and stores.   --
--                                                                    --
-- Unary and purely syntactic — it only has to deliver weak-head      --
-- normalization; soundness and head-faithfulness are separate.       --
--                                                                    --
-- `CRed` is an inductive family: `E` is an arbitrary preordered      --
-- monoid, so `op-grade op ·ₑ ε` need not exceed `ε` and there is no  --
-- measure to recurse on. Its induction carries FL's `handle` case.   --
--                                                                    --
-- Ground types have no arrows, so `VRedᵍ` comes first and `CRed`     --
-- precedes `VRed`, which instantiates it at the smaller predicate.   --
--                                                                    --
-- Both value predicates recurse on the type's *skeleton*, not the    --
-- type: at a box they speak of the raw store read, whose type the    --
-- cell declares and which `_<:ᵛ_` only relates to the payload type   --
-- named, shape-preservingly.                                         --
--                                                                    --
-- `CRed` is indexed by the skeleton too: a run refines the value      --
-- type, so the whnf it reaches is at a subtype of the one named.      --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.Reducibility (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.RenActions    Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec
open import Syntax.Terms.Transport       Spec
open import Syntax.Substitutions.Variables Spec
open import OperationalSemantics.Adequacy.GradedReach           Spec
open import Syntax.Substitutions.Equivalence Spec

-- A value of box type is a variable under a spine of subsumptions: the spine
-- leaves the variable alone, so the value still names a cell, but at the
-- cell's *declared* grade and payload type, which its own type only bounds.

val-cell : ∀ {Γ A ρ} → Γ ⊢V⦂ [ ρ ] A
         → Σ[ ρ₀ ∈ R ] Σ[ A₀ ∈ VType ] Var Γ ([ ρ₀ ] A₀)
val-cell {A = A} {ρ = ρ} (var {ρ = σ} _ x) = ρ , A , σ , x
val-cell (subV V ([ _ ]ₛ _))               = val-cell V

cellᵛ : ∀ {Γ A ρ} → (V : Γ ⊢V⦂ [ ρ ] A)
      → [ proj₁ (val-cell V) ] proj₁ (proj₂ (val-cell V))
          ∈[ proj₁ (proj₂ (proj₂ (val-cell V))) ] Γ
cellᵛ V = proj₂ (proj₂ (proj₂ (val-cell V)))

-- The cell's declared payload type, and the spine as a single subsumption.

val-typeᵛ : ∀ {Γ A ρ} → Γ ⊢V⦂ [ ρ ] A → VType
val-typeᵛ V = proj₁ (proj₂ (val-cell V))

val-subᵛ : ∀ {Γ A ρ} → (V : Γ ⊢V⦂ [ ρ ] A) → val-typeᵛ V <:ᵛ A
val-subᵛ {A = A} (var _ x)   = <:ᵛ-refl A
val-subᵛ (subV V ([ _ ]ₛ p)) = <:ᵛ-trans (val-subᵛ V) p

-- The two projections commute with renaming and with a context equality.
-- Both are one-clause inductions; the variable clause is absurd.

fstᵛ-ren : ∀ {A B} {St St' : 𝕊 []} → (r : Ren [] (toCtx St') (toCtx St))
         → (V : toCtx St ⊢V⦂ A |×| B)
         → fstᵛ (V-rename r V) ≡ V-rename r (fstᵛ V)
fstᵛ-ren r (var _ x)             = ⊥-elim (⦉⦊-not-in-toCtx x)
fstᵛ-ren r ⦉ _ , _ ⦊             = refl
fstᵛ-ren r (subV V (p |×|ₛ _))   = cong (λ z → subV z p) (fstᵛ-ren r V)

sndᵛ-ren : ∀ {A B} {St St' : 𝕊 []} → (r : Ren [] (toCtx St') (toCtx St))
         → (V : toCtx St ⊢V⦂ A |×| B)
         → sndᵛ (V-rename r V) ≡ V-rename r (sndᵛ V)
sndᵛ-ren r (var _ x)             = ⊥-elim (⦉⦊-not-in-toCtx x)
sndᵛ-ren r ⦉ _ , _ ⦊             = refl
sndᵛ-ren r (subV V (_ |×|ₛ q))   = cong (λ z → subV z q) (sndᵛ-ren r V)

-- The skeleton a type shares with all its subtypes.

data Shape : Set where
  ⋆ˢ   : Shape
  _×ˢ_ : Shape → Shape → Shape
  _→ˢ_ : Shape → Shape → Shape
  □ˢ   : Shape → Shape

shapeᵛ : VType → Shape
shapeᵛ (Base b)      = ⋆ˢ
shapeᵛ Unit          = ⋆ˢ
shapeᵛ Bool          = ⋆ˢ
shapeᵛ (A |×| B)     = shapeᵛ A ×ˢ shapeᵛ B
shapeᵛ Empty         = ⋆ˢ
shapeᵛ (A ⇒ (B ‼ _)) = shapeᵛ A →ˢ shapeᵛ B
shapeᵛ ([ _ ] A)     = □ˢ (shapeᵛ A)

×ˢ-inj₁ : ∀ {t t' s s'} → (t ×ˢ t') ≡ (s ×ˢ s') → t ≡ s
×ˢ-inj₁ refl = refl

×ˢ-inj₂ : ∀ {t t' s s'} → (t ×ˢ t') ≡ (s ×ˢ s') → t' ≡ s'
×ˢ-inj₂ refl = refl

→ˢ-inj₁ : ∀ {t t' s s'} → (t →ˢ t') ≡ (s →ˢ s') → t ≡ s
→ˢ-inj₁ refl = refl

→ˢ-inj₂ : ∀ {t t' s s'} → (t →ˢ t') ≡ (s →ˢ s') → t' ≡ s'
→ˢ-inj₂ refl = refl

□ˢ-inj : ∀ {t s} → □ˢ t ≡ □ˢ s → t ≡ s
□ˢ-inj refl = refl

<:ᵛ-shape : ∀ {A A'} → A <:ᵛ A' → shapeᵛ A ≡ shapeᵛ A'
<:ᵛ-shape (Baseₛ _)       = refl
<:ᵛ-shape Unitₛ           = refl
<:ᵛ-shape Boolₛ           = refl
<:ᵛ-shape (p |×|ₛ q)      = cong₂ _×ˢ_ (<:ᵛ-shape p) (<:ᵛ-shape q)
<:ᵛ-shape Emptyₛ          = refl
<:ᵛ-shape (p ⇒ₛ (q ‼ₛ _)) = cong₂ _→ˢ_ (sym (<:ᵛ-shape p)) (<:ᵛ-shape q)
<:ᵛ-shape ([ _ ]ₛ p)      = cong □ˢ (<:ᵛ-shape p)

-- Ground types are the parameter and arity types of operations. They contain
-- no arrows, so the arrow clause is vacuous and this needs nothing but itself.

VRedᵍˢ : (t : Shape) → {A : VType} → shapeᵛ A ≡ t
       → (St : 𝕊 []) → toCtx St ⊢V⦂ A → Set

VRedᵍˢ ⋆ˢ        e St V = ⊤
VRedᵍˢ (t →ˢ t') e St V = ⊤

VRedᵍˢ (t ×ˢ t') {A |×| B}     e  St V =
  VRedᵍˢ t (×ˢ-inj₁ e) St (fstᵛ V) × VRedᵍˢ t' (×ˢ-inj₂ e) St (sndᵛ V)
VRedᵍˢ (t ×ˢ t') {Base b}      () St V
VRedᵍˢ (t ×ˢ t') {Unit}        () St V
VRedᵍˢ (t ×ˢ t') {Bool}        () St V
VRedᵍˢ (t ×ˢ t') {Empty}       () St V
VRedᵍˢ (t ×ˢ t') {A ⇒ (B ‼ ε)} () St V
VRedᵍˢ (t ×ˢ t') {[ ρ ] A}     () St V

VRedᵍˢ (□ˢ t) {[ ρ ] A}     e  St V =
  ∀ {St'} → (r : St [ cellᵛ V ]⊑ᶜ St')
  → VRedᵍˢ t (trans (<:ᵛ-shape (val-subᵛ V)) (□ˢ-inj e)) St' (lookupᶜ r)
VRedᵍˢ (□ˢ t) {Base b}      () St V
VRedᵍˢ (□ˢ t) {Unit}        () St V
VRedᵍˢ (□ˢ t) {Bool}        () St V
VRedᵍˢ (□ˢ t) {A |×| B}     () St V
VRedᵍˢ (□ˢ t) {Empty}       () St V
VRedᵍˢ (□ˢ t) {A ⇒ (B ‼ ε)} () St V

VRedᵍ : (G : GType) → (St : 𝕊 []) → toCtx St ⊢V⦂ type-of-gtype G → Set
VRedᵍ G = VRedᵍˢ (shapeᵛ (type-of-gtype G)) {type-of-gtype G} refl

-- `M` runs to a weak head normal form whose components are reducible. A step
-- refines the value type as well as the grade, so the whnf's own value type is
-- free and only its skeleton `s` is fixed; the refinement witness is stored as
-- the shape equality the whnf stands at.

VPred : Shape → Set₁
VPred s = {A : VType} → shapeᵛ A ≡ s → (St : 𝕊 []) → toCtx St ⊢V⦂ A → Set

data CRed (s : Shape) (P : VPred s)
     : {A : VType} → shapeᵛ A ≡ s
     → (ε : E) → (St : 𝕊 []) → toCtx St ⊢C⦂ A ‼ ε → Set where

  -- it returns a reducible value

  cred-ret : ∀ {A A₀ ε} {e : shapeᵛ A ≡ s} {St St₁ : 𝕊 []}
           → {M : toCtx St ⊢C⦂ A ‼ ε}
           → {V : toCtx St₁ ⊢V⦂ A₀}
           → (e₀ : shapeᵛ A₀ ≡ s)
           → ⟨ St , M ⟩ ↝* ⟨ St₁ , return V ⟩
           → P e₀ St₁ V
           ---------------------------------
           → CRed s P e ε St M

  -- or it gets stuck on an operation with a reducible parameter, whose
  -- resumption is reducible at every state where the operation's own grade
  -- has elapsed

  cred-op : ∀ {A A₀ ε ε₁} {e : shapeᵛ A ≡ s} {St St₁ : 𝕊 []} {op : Op}
          → {M : toCtx St ⊢C⦂ A ‼ ε}
          → {W : toCtx St₁ ⊢V⦂ type-of-gtype (param op)}
          → {M' : toCtx St₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                    ⊢C⦂ A₀ ‼ ε₁}
          → (e₀ : shapeᵛ A₀ ≡ s)
          → ⟨ St , M ⟩ ↝* ⟨ St₁ , perform op W M' ⟩
          → VRedᵍ (param op) St₁ W
          → (∀ {St₂ : 𝕊 []}
             → (q : St₁ ⊑ₛ[ mapᵉ (op-grade op) ] St₂)
             → (W' : toCtx St₂ ⊢V⦂ type-of-gtype (arity op))
             → VRedᵍ (arity op) St₂ W'
             → CRed s P e₀ ε₁ St₂ (resume q M' W'))
          -------------------------------------------------------------------
          → CRed s P e ε St M

-- Stated through the eliminators, so that subsumption is absorbed: a product
-- by its two projections, a function by what it does to a reducible argument
-- at a later state, a box by what reading its cell yields. Both `⇒` and
-- `[ ρ ]` are Kripke.

VRedˢ : (t : Shape) → {A : VType} → shapeᵛ A ≡ t
      → (St : 𝕊 []) → toCtx St ⊢V⦂ A → Set

VRedˢ ⋆ˢ e St V = ⊤

VRedˢ (t ×ˢ t') {A |×| B}     e  St V =
  VRedˢ t (×ˢ-inj₁ e) St (fstᵛ V) × VRedˢ t' (×ˢ-inj₂ e) St (sndᵛ V)
VRedˢ (t ×ˢ t') {Base b}      () St V
VRedˢ (t ×ˢ t') {Unit}        () St V
VRedˢ (t ×ˢ t') {Bool}        () St V
VRedˢ (t ×ˢ t') {Empty}       () St V
VRedˢ (t ×ˢ t') {A ⇒ (B ‼ ε)} () St V
VRedˢ (t ×ˢ t') {[ ρ ] A}     () St V

VRedˢ (t →ˢ t') {A ⇒ (B ‼ ε)} e  St V =
  ∀ {St'} → (q : St ⊑ₛ[ uᵣ ] St')
  → (W : toCtx St' ⊢V⦂ A)
  → VRedˢ t (→ˢ-inj₁ e) St' W
  → CRed t' (VRedˢ t') (→ˢ-inj₂ e) ε St' (reach-val q V · W)
VRedˢ (t →ˢ t') {Base b}      () St V
VRedˢ (t →ˢ t') {Unit}        () St V
VRedˢ (t →ˢ t') {Bool}        () St V
VRedˢ (t →ˢ t') {A |×| B}     () St V
VRedˢ (t →ˢ t') {Empty}       () St V
VRedˢ (t →ˢ t') {[ ρ ] A}     () St V

VRedˢ (□ˢ t) {[ ρ ] A}     e  St V =
  ∀ {St'} → (r : St [ cellᵛ V ]⊑ᶜ St')
  → VRedˢ t (trans (<:ᵛ-shape (val-subᵛ V)) (□ˢ-inj e)) St' (lookupᶜ r)
VRedˢ (□ˢ t) {Base b}      () St V
VRedˢ (□ˢ t) {Unit}        () St V
VRedˢ (□ˢ t) {Bool}        () St V
VRedˢ (□ˢ t) {A |×| B}     () St V
VRedˢ (□ˢ t) {Empty}       () St V
VRedˢ (□ˢ t) {A ⇒ (B ‼ ε)} () St V

VRed : (A : VType) → (St : 𝕊 []) → toCtx St ⊢V⦂ A → Set
VRed A = VRedˢ (shapeᵛ A) {A} refl

-- Reducible computations at the value predicate `VRed` — the form the
-- fundamental lemma proves. Stated at a shape, so that a subsumption moves the
-- equality index and leaves the predicate alone.

CRedˢ' : (s : Shape) → {A : VType} → shapeᵛ A ≡ s
       → (ε : E) → (St : 𝕊 []) → toCtx St ⊢C⦂ A ‼ ε → Set
CRedˢ' s = CRed s (VRedˢ s)

CRed' : (A : VType) → (ε : E) → (St : 𝕊 []) → toCtx St ⊢C⦂ A ‼ ε → Set
CRed' A = CRedˢ' (shapeᵛ A) {A} refl

-- Two proofs of a shape equality out of the same type carry the predicate
-- across, by UIP on the shared endpoints.

VRedˢ-≡ˢ : ∀ {t t' A} {St : 𝕊 []} {V : toCtx St ⊢V⦂ A}
         → {e : shapeᵛ A ≡ t} → {e' : shapeᵛ A ≡ t'}
         → VRedˢ t e St V → VRedˢ t' e' St V
VRedˢ-≡ˢ {e = refl} {e' = refl} p = p

VRedˢ-≡ᵛ : ∀ {t A} {St : 𝕊 []} {e : shapeᵛ A ≡ t} {V V' : toCtx St ⊢V⦂ A}
         → V ≡ V' → VRedˢ t e St V → VRedˢ t e St V'
VRedˢ-≡ᵛ refl p = p

CRedˢ'-≡ˢ : ∀ {t t' A ε} {St : 𝕊 []} {M : toCtx St ⊢C⦂ A ‼ ε}
          → {e : shapeᵛ A ≡ t} → {e' : shapeᵛ A ≡ t'}
          → CRedˢ' t e ε St M → CRedˢ' t' e' ε St M
CRedˢ'-≡ˢ {e = refl} {e' = refl} p = p

-- Every cell of the state holds a value that is reducible at any later state
-- at which it is readable.

SRed : 𝕊 [] → Set
SRed St = ∀ {A ρ σ} {St' : 𝕊 []} → (c : [ ρ ] A ∈[ σ ] toCtx St)
        → (r : St [ c ]⊑ᶜ St')
        → VRed A St' (lookupᶜ r)

-- A step in front of a reducible computation reaches the same whnf by a
-- longer run. `CRed` carries runs, so `_◅_` leaves the grade and the value
-- type free; only the stored shape equality is kept.

CRed-expand : ∀ {s} {P : VPred s} {A A₀ ε ε₀} {St St₀ : 𝕊 []}
            → {e : shapeᵛ A ≡ s} → {e₀ : shapeᵛ A₀ ≡ s}
            → {M : toCtx St ⊢C⦂ A ‼ ε} → {M₀ : toCtx St₀ ⊢C⦂ A₀ ‼ ε₀}
            → ⟨ St , M ⟩ ↝ ⟨ St₀ , M₀ ⟩
            → CRed s P e₀ ε₀ St₀ M₀
            -------------------------
            → CRed s P e ε St M

CRed-expand r (cred-ret e₀ rs pV)   = cred-ret e₀ (r ◅ rs) pV
CRed-expand r (cred-op e₀ rs pW pk) = cred-op e₀ (r ◅ rs) pW pk

-- A whole run in front of a reducible computation, and transporting one along an
-- equality of effects (which `SEQ-OP`'s reduct carries).

CRed-expand* : ∀ {s} {P : VPred s} {A A₀ ε ε₀} {St St₀ : 𝕊 []}
             → {e : shapeᵛ A ≡ s} → {e₀ : shapeᵛ A₀ ≡ s}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M₀ : toCtx St₀ ⊢C⦂ A₀ ‼ ε₀}
             → ⟨ St , M ⟩ ↝* ⟨ St₀ , M₀ ⟩
             → CRed s P e₀ ε₀ St₀ M₀
             -------------------------
             → CRed s P e ε St M

CRed-expand* {s = s} {P = P} {ε = ε} {St = St} {M = M} ε* p =
  subst (λ z → CRed s P z ε St M) uip p
CRed-expand* {e = e} (r ◅ rs) p =
  CRed-expand r
    (CRed-expand* {e = trans (<:ᵛ-shape (step-refines-type r)) e} rs p)

CRed-ε-subst : ∀ {s} {P : VPred s} {A ε ε'} {e : shapeᵛ A ≡ s} {St : 𝕊 []}
             → (eε : ε ≡ ε') → {M : toCtx St ⊢C⦂ A ‼ ε}
             → CRed s P e ε St M → CRed s P e ε' St (ε-subst eε M)
CRed-ε-subst refl p = p

-- Reducibility is monotone in the subtyping order. Both halves are stated at a
-- fixed skeleton, the subtyping witness moving the equality index alone. The
-- value half recurses on the witness; at an arrow `SUB-APP` splits the witness
-- across the application, the codomain half becoming the step's refinement. At
-- a box both sides quantify over the same reads of the same cell.

VRedˢ-sub : ∀ {s A A'} {e : shapeᵛ A ≡ s} {e' : shapeᵛ A' ≡ s} {St : 𝕊 []}
          → (p : A <:ᵛ A') → (V : toCtx St ⊢V⦂ A)
          → VRedˢ s e St V → VRedˢ s e' St (subV V p)

VRedˢ-sub {e' = refl} (Baseₛ refl) V pV         = tt
VRedˢ-sub {e' = refl} Unitₛ        V pV         = tt
VRedˢ-sub {e' = refl} Boolₛ        V pV         = tt
VRedˢ-sub {e' = refl} Emptyₛ       V pV         = tt
VRedˢ-sub {e' = refl} (p |×|ₛ p')  V (pV , pV') =
  VRedˢ-sub p (fstᵛ V) pV , VRedˢ-sub p' (sndᵛ V) pV'
VRedˢ-sub {e' = refl} (p ⇒ₛ (p' ‼ₛ q)) V f      =
  λ q₀ W pW → CRed-expand SUB-APP (f q₀ (subV W p) (VRedˢ-sub p W pW))
VRedˢ-sub {e' = refl} ([ _ ]ₛ p)   V f          = λ r → VRedˢ-≡ˢ (f r)

VRed-sub : ∀ {A A'} {St : 𝕊 []} → (p : A <:ᵛ A')
         → (V : toCtx St ⊢V⦂ A) → VRed A St V → VRed A' St (subV V p)

VRed-sub p V pV = VRedˢ-sub {e = <:ᵛ-shape p} p V (VRedˢ-≡ˢ pV)

-- A run refines the value type one subsumption at a time, and `spine` applies
-- them in order; reducibility travels along it.

VRed-spine : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
           → (rs : cf ↝* cf') → {St : 𝕊 []} → (V : toCtx St ⊢V⦂ B)
           → VRed B St V → VRed A St (spine rs V)

VRed-spine ε*       V pV = pV
VRed-spine (r ◅ rs) V pV =
  VRed-sub (step-refines-type r) (spine rs V) (VRed-spine rs V pV)

-- A subsumed computation is its own reduct, one `SUB` step on.

CRed-sub : ∀ {s A A' ε ε₀} {e : shapeᵛ A ≡ s} {e' : shapeᵛ A' ≡ s} {St : 𝕊 []}
         → (p : A <:ᵛ A') → (q : ε ≾ₑ ε₀)
         → {M : toCtx St ⊢C⦂ A ‼ ε}
         → CRedˢ' s e ε St M → CRedˢ' s e' ε₀ St (subC M (p ‼ₛ q))

CRed-sub p q = CRed-expand SUB

CRed'-sub : ∀ {A A' ε ε₀} {St : 𝕊 []} → (p : A <:ᵛ A') → (q : ε ≾ₑ ε₀)
          → {M : toCtx St ⊢C⦂ A ‼ ε}
          → CRed' A ε St M → CRed' A' ε₀ St (subC M (p ‼ₛ q))

CRed'-sub p q pM = CRed-sub {e = <:ᵛ-shape p} p q (CRedˢ'-≡ˢ pM)

-- The empty store: `toCtx ∅` has no variables.

SRed-∅ : SRed ∅
SRed-∅ c r = ⊥-elim (not-in-empty-ctx c)

-- A boolean over a state context runs to one of the two constants: a variable
-- is ruled out by `Bool-not-in-toCtx`, and a subsumption is dropped by
-- `SUB-IF`.

bool-canonical : ∀ {St : 𝕊 []} → (V : toCtx St ⊢V⦂ Bool)
               → (∀ {A ε} {M N : toCtx St ⊢C⦂ A ‼ ε}
                    → ⟨ St , if V `then M `else N ⟩ ↝* ⟨ St , M ⟩)
               ⊎ (∀ {A ε} {M N : toCtx St ⊢C⦂ A ‼ ε}
                    → ⟨ St , if V `then M `else N ⟩ ↝* ⟨ St , N ⟩)
bool-canonical (var f x)      = ⊥-elim (Bool-not-in-toCtx x)
bool-canonical true           = inj₁ (IF-TRUE ◅ ε*)
bool-canonical false          = inj₂ (IF-FALSE ◅ ε*)
bool-canonical (subV V Boolₛ) with bool-canonical V
... | inj₁ rs = inj₁ (SUB-IF ◅ rs)
... | inj₂ rs = inj₂ (SUB-IF ◅ rs)

-- An eternal type is built from base, unit, empty and products, so `VRed`
-- asks nothing of a value of eternal type.

VRed-eternal : ∀ {A} {St : 𝕊 []} → Eternal A → (V : toCtx St ⊢V⦂ A) → VRed A St V

VRed-eternal (Baseₑ _)        V = tt
VRed-eternal Unitₑ            V = tt
VRed-eternal Boolₑ            V = tt
VRed-eternal Emptyₑ           V = tt
VRed-eternal (et₁ |×|ₑ et₂)   V =
  VRed-eternal et₁ (fstᵛ V) , VRed-eternal et₂ (sndᵛ V)

VRed-≡ᵛ : ∀ {St : 𝕊 []} → (A : VType) → {V V' : toCtx St ⊢V⦂ A}
        → V ≡ V' → VRed A St V → VRed A St V'

VRed-≡ᵛ A refl p = p

-- Reading a cell after a reach is reading it before: the payload is the same
-- value, so what holds of it transports. An induction on the value — the spine
-- passes it on, and the variable clause is where the reach is absorbed.

reach-read-val : ∀ {t A ρ} {St St' : 𝕊 []} → (q : St ⊑ₛ[ uᵣ ] St')
               → (V : toCtx St ⊢V⦂ [ ρ ] A)
               → (e : shapeᵛ (val-typeᵛ V) ≡ t)
               → (e' : shapeᵛ (val-typeᵛ (reach-val q V)) ≡ t)
               → (∀ {St₂ : 𝕊 []} → (r₀ : St [ cellᵛ V ]⊑ᶜ St₂)
                    → VRedˢ t e St₂ (lookupᶜ r₀))
               -------------------------------------------------------------
               → ∀ {St₂ : 𝕊 []} → (r : St' [ cellᵛ (reach-val q V) ]⊑ᶜ St₂)
               → VRedˢ t e' St₂ (lookupᶜ r)

reach-read-val {ρ = ρ} q (var _ x) e e' h {St₂} (read ee rel) =
  VRedˢ-≡ˢ (VRedˢ-≡ᵛ (lookup-body-≡ St₂ cellEq rel₁ rel)
                     (h (read (≤ₛ-trans (ext q) ee) rel₁)))
  where
    cellEq = trans (≤ₛ-embed-∘ (ext q) ee x)
                   (sym (cong (λ z → ≤ₛ-embed ee (proj₂ z))
                              (reach-renᵘ-img q x)))
    rel₁ = subst (_≾ᵣ ρ) (sym (cong proj₁ cellEq)) rel

reach-read-val q (subV V ([ _ ]ₛ _)) e e' h r = reach-read-val q V e e' h r

VRedˢ-reach : ∀ {t A} {St St' : 𝕊 []} → (q : St ⊑ₛ[ uᵣ ] St')
            → (e : shapeᵛ A ≡ t) → (V : toCtx St ⊢V⦂ A)
            → VRedˢ t e St V → VRedˢ t e St' (reach-val q V)

VRedˢ-reach {⋆ˢ} q e V p = tt

VRedˢ-reach {t ×ˢ t'} {A |×| B}     q e  V (p₁ , p₂) =
    VRedˢ-≡ᵛ (sym (fstᵛ-ren (reach-renᵘ q) V))
             (VRedˢ-reach q (×ˢ-inj₁ e) (fstᵛ V) p₁)
  , VRedˢ-≡ᵛ (sym (sndᵛ-ren (reach-renᵘ q) V))
             (VRedˢ-reach q (×ˢ-inj₂ e) (sndᵛ V) p₂)
VRedˢ-reach {t ×ˢ t'} {Base b}      q () V p
VRedˢ-reach {t ×ˢ t'} {Unit}        q () V p
VRedˢ-reach {t ×ˢ t'} {Bool}        q () V p
VRedˢ-reach {t ×ˢ t'} {Empty}       q () V p
VRedˢ-reach {t ×ˢ t'} {A ⇒ (B ‼ ε)} q () V p
VRedˢ-reach {t ×ˢ t'} {[ ρ ] A}     q () V p

VRedˢ-reach {t →ˢ t'} {A ⇒ (B ‼ ε)} q₀ e  V f = λ q' W pW →
  subst (λ z → CRed t' (VRedˢ t') (→ˢ-inj₂ e) ε _ (z · W))
        (trans (V-rename-≡ (reach-renᵘ-∘ q' q₀) V)
               (V-rename-∘ (reach-renᵘ q₀) (reach-renᵘ q') V))
        (f (reach-∘ q' q₀) W pW)
VRedˢ-reach {t →ˢ t'} {Base b}      q () V f
VRedˢ-reach {t →ˢ t'} {Unit}        q () V f
VRedˢ-reach {t →ˢ t'} {Bool}        q () V f
VRedˢ-reach {t →ˢ t'} {A |×| B}     q () V f
VRedˢ-reach {t →ˢ t'} {Empty}       q () V f
VRedˢ-reach {t →ˢ t'} {[ ρ ] A}     q () V f

VRedˢ-reach {□ˢ t} {[ ρ ] A}     q e  V f = reach-read-val q V _ _ f
VRedˢ-reach {□ˢ t} {Base b}      q () V f
VRedˢ-reach {□ˢ t} {Unit}        q () V f
VRedˢ-reach {□ˢ t} {Bool}        q () V f
VRedˢ-reach {□ˢ t} {A |×| B}     q () V f
VRedˢ-reach {□ˢ t} {Empty}       q () V f
VRedˢ-reach {□ˢ t} {A ⇒ (B ‼ ε)} q () V f

VRed-reach : ∀ {A St St'} → (q : St ⊑ₛ[ uᵣ ] St') → (V : toCtx St ⊢V⦂ A)
           → VRed A St V → VRed A St' (reach-val q V)

VRed-reach q V p = VRedˢ-reach q refl V p

-- `VRedᵍ` is `VRed` restricted to the ground types, whose skeletons have no
-- arrows, so the two predicates coincide clause for clause. Two recursions on
-- the ground type, with the value's own type left free — a box's read is at
-- the cell's declared type, not the one named.

VRedˢ→VRedᵍˢ : (G : GType) → ∀ {A} {St : 𝕊 []}
             → (e : shapeᵛ A ≡ shapeᵛ (type-of-gtype G))
             → (V : toCtx St ⊢V⦂ A)
             → VRedˢ (shapeᵛ (type-of-gtype G)) e St V
             → VRedᵍˢ (shapeᵛ (type-of-gtype G)) e St V

VRedˢ→VRedᵍˢ (Base b) e V p = tt
VRedˢ→VRedᵍˢ Unit     e V p = tt
VRedˢ→VRedᵍˢ Bool     e V p = tt
VRedˢ→VRedᵍˢ Empty    e V p = tt

VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {A |×| B}     e  V (p₁ , p₂) =
    VRedˢ→VRedᵍˢ G₁ (×ˢ-inj₁ e) (fstᵛ V) p₁
  , VRedˢ→VRedᵍˢ G₂ (×ˢ-inj₂ e) (sndᵛ V) p₂
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {Base b}      () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {Unit}        () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {Bool}        () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {Empty}       () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {A ⇒ (B ‼ ε)} () V p
VRedˢ→VRedᵍˢ (G₁ |×|ᵍ G₂) {[ ρ ] A}     () V p

VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {[ ρ ] A}     e  V p =
  λ r → VRedˢ→VRedᵍˢ G _ (lookupᶜ r) (p r)
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {Base b}      () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {Unit}        () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {Bool}        () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {A |×| B}     () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {Empty}       () V p
VRedˢ→VRedᵍˢ ([ ρ₀ ]ᵍ G) {A ⇒ (B ‼ ε)} () V p

VRedᵍˢ→VRedˢ : (G : GType) → ∀ {A} {St : 𝕊 []}
             → (e : shapeᵛ A ≡ shapeᵛ (type-of-gtype G))
             → (V : toCtx St ⊢V⦂ A)
             → VRedᵍˢ (shapeᵛ (type-of-gtype G)) e St V
             → VRedˢ (shapeᵛ (type-of-gtype G)) e St V

VRedᵍˢ→VRedˢ (Base b) e V p = tt
VRedᵍˢ→VRedˢ Unit     e V p = tt
VRedᵍˢ→VRedˢ Bool     e V p = tt
VRedᵍˢ→VRedˢ Empty    e V p = tt

VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {A |×| B}     e  V (p₁ , p₂) =
    VRedᵍˢ→VRedˢ G₁ (×ˢ-inj₁ e) (fstᵛ V) p₁
  , VRedᵍˢ→VRedˢ G₂ (×ˢ-inj₂ e) (sndᵛ V) p₂
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {Base b}      () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {Unit}        () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {Bool}        () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {Empty}       () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {A ⇒ (B ‼ ε)} () V p
VRedᵍˢ→VRedˢ (G₁ |×|ᵍ G₂) {[ ρ ] A}     () V p

VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {[ ρ ] A}     e  V p =
  λ r → VRedᵍˢ→VRedˢ G _ (lookupᶜ r) (p r)
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {Base b}      () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {Unit}        () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {Bool}        () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {A |×| B}     () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {Empty}       () V p
VRedᵍˢ→VRedˢ ([ ρ₀ ]ᵍ G) {A ⇒ (B ‼ ε)} () V p

VRed→VRedᵍ : (G : GType) → {St : 𝕊 []} → (V : toCtx St ⊢V⦂ type-of-gtype G)
           → VRed (type-of-gtype G) St V → VRedᵍ G St V

VRed→VRedᵍ G V p = VRedˢ→VRedᵍˢ G refl V p

VRedᵍ→VRed : (G : GType) → {St : 𝕊 []} → (V : toCtx St ⊢V⦂ type-of-gtype G)
           → VRedᵍ G St V → VRed (type-of-gtype G) St V

VRedᵍ→VRed G V p = VRedᵍˢ→VRedˢ G refl V p

-- Ground reducibility is insensitive to the equivalence, as `VRed-≡ᵛ` is.

VRedᵍ-≡ᵛ : ∀ {St : 𝕊 []} → (G : GType) → {V V' : toCtx St ⊢V⦂ type-of-gtype G}
         → V ≡ V' → VRedᵍ G St V → VRedᵍ G St V'

VRedᵍ-≡ᵛ G refl p = p

-- Reducibility is insensitive to the term equivalence.

CRed-≡ᶜ : ∀ {A ε} {St : 𝕊 []} {M M' : toCtx St ⊢C⦂ A ‼ ε}
        → M ≡ M' → CRed' A ε St M → CRed' A ε St M'
CRed-≡ᶜ refl p = p

-- Handling is `Adequacy.Handle`, above `Environment`: as sequencing, plus a
-- clause premise, and needing `sub-wk-C` for the same reason.

-- The freshly allocated cell is reducible: a reach out of `St ∷ₛ V` at `ρ`
-- is one out of `St`, and reading the cell back returns the stored value.

SRed-fresh : ∀ {A ρ} {St : 𝕊 []} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
           → (∀ {St'} → (q : St ⊑ₛ[ ρ ] St')
                → VRed A St' (V-rename (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q) V))
           → (f : ¬ Eternal ([ ρ ] A) → uᵣ ≾ᵣ uᵣ)
           ------------------------------------------
           → VRed ([ ρ ] A) (St ∷ₛ V) (var f Hd)

SRed-fresh {A} {ρ} {St} V pV f {St'} r =
  VRedˢ-≡ˢ (VRed-≡ᵛ A (sym (alloc-lookup-≡ V (extᶜ r) (ready r) q₀ refl))
                      (pV q₀))
  where
    e   = extᶜ r
    rel = ready r
    -- the allocation accumulates nothing, so the cell's readability at `St'`
    -- *is* the bound the reach back to `St` needs
    q₀ : St ⊑ₛ[ ρ ] St'
    q₀ = reach (≤ₛ-trans (∷-suc V id-suc) e)
               (≾ᵣ-trans
                 (≾ᵣ-reflexive
                   (trans (≤ₛ-grade-trans (∷-suc V id-suc) e)
                          (sym (≤ₛ-embed-grade e (Hd {Γ = toCtx St})))))
                 rel)

-- Every variable of a state context is of box type, so at the other four
-- types there is nothing to show. At a box type a usable variable is
-- reducible via the store read at the states its own box grade allows.

SRed-var : ∀ {A ρ} {St : 𝕊 []} → SRed St
         → (x : A ∈[ ρ ] toCtx St) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
         --------------------------------------------------------
         → VRed A St (var f x)

SRed-var {Base b}    pSt x f = tt
SRed-var {Unit}      pSt x f = tt
SRed-var {Bool}      pSt x f = tt
SRed-var {Empty}     pSt x f = tt
SRed-var {A₁ |×| A₂} pSt x f = ⊥-elim (⦉⦊-not-in-toCtx x)
SRed-var {A₁ ⇒ C}    pSt x f = ⊥-elim (⇒-not-in-toCtx x)

SRed-var {[ ρ ] A} pSt x f r = VRedˢ-≡ˢ (pSt x r)
