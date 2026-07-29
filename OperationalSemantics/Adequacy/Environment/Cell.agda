------------------------------------------------------------------------
-- The action on the cell an `unbox` names.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (yes; no; ¬_; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.Environment.Cell (Spec : LanguageSpec) where

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

open import OperationalSemantics.Adequacy.Reducibility   Spec
open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec
open import Syntax.Terms.Transport       Spec
open import Syntax.Substitutions.Variables Spec
open import Syntax.Substitutions.Weakening Spec
open import Syntax.Substitutions.Renaming  Spec
open import Syntax.Substitutions.Swap      Spec
open import OperationalSemantics.Adequacy.Slice          Spec
open import Syntax.Substitutions.Equivalence Spec
open import OperationalSemantics.Adequacy.Environment.Core Spec
open import OperationalSemantics.Adequacy.Environment.Action Spec
open import OperationalSemantics.Adequacy.Environment.Variables Spec
open import OperationalSemantics.Adequacy.Environment.Clauses Spec

------------------------------------------------------------------------
-- THE ACTION ON THE CELL AN `unbox` NAMES
--
-- Reduction consults an `unbox` only through its cell (`unbox-tgt`), and that
-- is also all `_≐ᶜ_` compares, so this is what the action does to an `unbox`.
-- The zones that rename move the cell by `var-tgt′`; the zones that substitute
-- move it by `⟨_⟩[_↦_]rvar`, the value put in a resource variable's place
-- being of box type and hence itself a variable.
--
-- Only the cell is tracked, not its grade bound: `unbox-var-≐` does not see the
-- bound, so every consumer recovers whichever bound it needs from the term.
------------------------------------------------------------------------

-- one step of the eternal zone's chain

env-eternal-cell : ∀ {Δ Γc A ρ} → Lock-free Δ → ClosedVals Δ
                 → Tgt (Δ ++ᶜ Γc) ([ ρ ] A) → Tgt Γc ([ ρ ] A)

env-eternal-cell lf-[] η t = Tgt-cast ++ᶜ-identityˡ t

env-eternal-cell {Δ ∷ B} {Γc} (lf-∷ lf) η (σ , z) =
  env-eternal-cell lf (λ x → η (Tl-∷ x))
    (Tgt-cast (castOf {Δ} {B} Γc)
      (proj₁ (⟨ z ⟩[ bvar B Γc ↦ bval Γc (V-rename (empty-ren lf) (η Hd)) ]rvar)
      , proj₁ (proj₂ (⟨ z ⟩[ bvar B Γc
                             ↦ bval Γc (V-rename (empty-ren lf) (η Hd)) ]rvar))))

env-cell : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx)
         → Tgt (Γ ++ᶜ Δ) ([ ρ ] A) → Tgt (toCtx St ++ᶜ Δ) ([ ρ ] A)

env-cell ⌊ St ⌋      Δ t = t
env-cell (∅ᵉ St)     Δ t = var-tgt′ (cong-ren (∅-ren St)) t
env-cell (sliceᵉ γ q) Δ t =
  var-tgt′ (cong-ren (slice-renᵘ q)) (env-cell γ Δ t)

env-cell (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ t =
  var-tgt′ (cong-ren (unbox-ren q))
    (Tgt-cast (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ))
      (env-cell γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
        (Tgt-cast (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) t)))

env-cell (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ t =
  Tgt-cast (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ₀ ] A₀) Δ))
    (env-cell γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
      (Tgt-cast (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) t))

env-cell (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ t =
  Tgt-cast (castOf {toCtx St} {A₀} Δ)
    (proj₁ (⟨ z ⟩[ bvar A₀ Δ ↦ bval Δ W ]rvar)
    , proj₁ (proj₂ (⟨ z ⟩[ bvar A₀ Δ ↦ bval Δ W ]rvar)))
  where
    z = proj₂ (Tgt-cast (sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ))
                 (env-cell γ ([] ∷ A₀ ++ᶜ Δ)
                   (Tgt-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t)))

env-cell (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ t =
  env-cell γ Δ
    (env-eternal-cell lf η (Tgt-cast (++ᶜ-assoc Δ₀ Γ₁ Δ) t))

-- The readability bound travels with the cell. Renaming a variable can only
-- lower its grade (`var-rename`'s own bound, discharged at a box type, which is
-- never eternal), and `⟨_⟩[_↦_]rvar` carries its bound as its third component —
-- so a cell readable at `ρ` stays readable at `ρ` wherever the action puts it.

var-tgt-≾ : ∀ {Γ Γ' A ρ σ} → (r : Ren [] Γ Γ')
          → (x : [ ρ ] A ∈[ σ ] Γ) → proj₁ (var-tgt r x) ≾ᵣ σ
var-tgt-≾ r x = proj₁ (proj₂ (var-rename r x)) (λ ())

env-eternal-cell-rel : ∀ {Δ Γc A ρ} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                     → (t : Tgt (Δ ++ᶜ Γc) ([ ρ ] A))
                     → proj₁ t ≾ᵣ ρ
                     → proj₁ (env-eternal-cell lf η t) ≾ᵣ ρ

env-eternal-cell-rel lf-[] η t rel = rel

env-eternal-cell-rel {Δ ∷ B} {Γc} (lf-∷ lf) η (σ , z) rel =
  env-eternal-cell-rel lf (λ x → η (Tl-∷ x)) _
    (≾ᵣ-trans
      (proj₂ (proj₂ (⟨ z ⟩[ bvar B Γc
                            ↦ bval Γc (V-rename (empty-ren lf) (η Hd)) ]rvar)))
      rel)

env-cell-rel : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx)
             → (t : Tgt (Γ ++ᶜ Δ) ([ ρ ] A))
             → proj₁ t ≾ᵣ ρ
             → proj₁ (env-cell γ Δ t) ≾ᵣ ρ

env-cell-rel ⌊ St ⌋       Δ t rel = rel
env-cell-rel (∅ᵉ St)      Δ t rel =
  ≾ᵣ-trans (var-tgt-≾ (cong-ren (∅-ren St)) (proj₂ t)) rel
env-cell-rel (sliceᵉ γ q) Δ t rel =
  ≾ᵣ-trans (var-tgt-≾ (cong-ren (slice-renᵘ q)) (proj₂ (env-cell γ Δ t)))
           (env-cell-rel γ Δ t rel)

env-cell-rel (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ t rel =
  ≾ᵣ-trans (var-tgt-≾ (cong-ren (unbox-ren q)) z)
           (env-cell-rel γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
                         (Tgt-cast (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) t) rel)
  where
    z = proj₂ (Tgt-cast (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ))
                 (env-cell γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
                   (Tgt-cast (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) t)))

env-cell-rel (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ t rel =
  env-cell-rel γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
               (Tgt-cast (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) t) rel

env-cell-rel (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ t rel =
  ≾ᵣ-trans
    (proj₂ (proj₂ (⟨ z ⟩[ bvar A₀ Δ ↦ bval Δ W ]rvar)))
    (env-cell-rel γ ([] ∷ A₀ ++ᶜ Δ) (Tgt-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t) rel)
  where
    z = proj₂ (Tgt-cast (sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ))
                 (env-cell γ ([] ∷ A₀ ++ᶜ Δ)
                   (Tgt-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t)))

env-cell-rel (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ t rel =
  env-cell-rel γ Δ _
    (env-eternal-cell-rel lf η (Tgt-cast (++ᶜ-assoc Δ₀ Γ₁ Δ) t) rel)

-- and the same on computations, zone for zone

env-Cˢ-≐ : ∀ {St Γ C} → (γ : Env St Γ) → (Δ : Ctx) → {M M' : (Γ ++ᶜ Δ) ⊢C⦂ C}
         → M ≐ᶜ M' → env-Cˢ γ Δ M ≐ᶜ env-Cˢ γ Δ M'

env-Cˢ-≐ ⌊ St ⌋       Δ eM = eM
env-Cˢ-≐ (∅ᵉ St)      Δ eM = C-rename-cong _ eM
env-Cˢ-≐ (sliceᵉ γ q) Δ eM = C-rename-cong _ (env-Cˢ-≐ γ Δ eM)
env-Cˢ-≐ (γ ⟨ q ⟩ᵉ)   Δ eM =
  C-rename-cong _ (castᶜ-≐ _ (env-Cˢ-≐ γ _ (castᶜ-≐ _ eM)))
env-Cˢ-≐ (liftᵉ V γ)  Δ eM = castᶜ-≐ _ (env-Cˢ-≐ γ _ (castᶜ-≐ _ eM))
env-Cˢ-≐ (_∷ᵉ_ {St = St} {Γ = Γ} {A = A} γ W) Δ eM =
  castᶜ-≐ (cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t))
    (sub-≐ᶜ (split→∈ t) (≐ᵛ-refl (castᵛ (sym (split→∈-split-l t)) W))
      (castᶜ-≐ (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))
        (env-Cˢ-≐ γ ([] ∷ A ++ᶜ Δ) (castᶜ-≐ (++ᶜ-assoc Γ ([] ∷ A) Δ) eM))))
  where
    t = split-≡-++ᶜ {toCtx St ∷ A} {Δ}
env-Cˢ-≐ (eternalˡ Δ₀ lf η γ) Δ eM =
  env-Cˢ-≐ γ Δ (env-eternal-C-≐ lf η (castᶜ-≐ _ eM))

------------------------------------------------------------------------
-- THE ACTION COMMUTES WITH `unbox`
--
-- The action sends an `unbox` to an `unbox` at the cell `env-cell` computes.
-- Only up to `_≐ᶜ_`, and necessarily so: the renaming zones compose their
-- renaming into the one the node stores, while the substituting zones
-- renormalise the node entirely (`unbox⇒var` then `unbox-var`), so the stored
-- renaming and boxed value do not agree on the nose — which is exactly why
-- `unbox-≐` compares the cell alone.
------------------------------------------------------------------------

-- Recognising a node by its cell.

unbox-cell-≐ : ∀ {Γ A C ρ Δ₀ σ} → {w : Ren [] (Δ₀ ⟨ ρ ⟩) Γ} → {V : Δ₀ ⊢V⦂ [ ρ ] A}
             → {z : [ ρ ] A ∈[ σ ] Γ} → (rel : σ ≾ᵣ ρ)
             → unbox-tgt w V ≡ (σ , z)
             → {N N' : Γ ∷ A ⊢C⦂ C} → N ≐ᶜ N'
             → unbox w V N ≐ᶜ unbox-var z rel N'
unbox-cell-≐ rel eq eN = unbox-≐ (trans eq (sym (unbox-var-tgt _ rel))) eN

-- and moving a recognised node along a transport of its context

unbox-var-cast-≐ : ∀ {Γ Γ' A C ρ} → (e : Γ ≡ Γ') → (t : Tgt Γ ([ ρ ] A))
                 → (rel rel' : proj₁ t ≾ᵣ ρ)
                 → (N : Γ ∷ A ⊢C⦂ C)
                 → castᶜ e (unbox-var (proj₂ t) rel N)
                 ≐ᶜ unbox-var (proj₂ (Tgt-cast e t)) rel'
                              (castᶜ (cong (_∷ A) e) N)
unbox-var-cast-≐ refl t rel rel' N = unbox-var-≐ (proj₂ t) rel rel' (≐ᶜ-refl N)

------------------------------------------------------------------------
-- THE ACTION COMMUTES WITH `unbox`
--
-- The action sends an `unbox` to an `unbox` at the cell `env-cell` computes.
-- Only up to `_≐ᶜ_`, and necessarily so: the renaming zones compose their
-- renaming into the one the node stores, while the substituting zones
-- renormalise the node entirely (`unbox⇒var` then `unbox-var`), so the stored
-- renaming and boxed value do not agree on the nose — which is why `unbox-≐`
-- compares the cell alone.
--
-- The node is *returned*, together with its cell, rather than presented as an
-- `unbox-var`. Otherwise every zone's intermediate term carries a `≾ᵣ` bound
-- that unification cannot recover — `unbox-var` stores its renaming through
-- `split-pf`, so it is not invertible — and there are two such bounds per zone.
-- Returning the node keeps every bound out of the chain but one, `sub-unbox`'s,
-- which the input bound supplies explicitly through `env-cell-rel`.
--
-- The cell is a parameter given by an equation, since a substituting zone
-- retargets it: its cell is `unbox-var-tgt` of the rebuilt node.
------------------------------------------------------------------------

UnboxAt : ∀ {St Γ A C ρ} → (γ : Env St Γ) → (Δ : Ctx)
        → Tgt (Γ ++ᶜ Δ) ([ ρ ] A)
        → toCtx St ++ᶜ Δ ⊢C⦂ C → ((Γ ++ᶜ Δ) ∷ A) ⊢C⦂ C → Set
UnboxAt {St} {Γ} {A} {C} {ρ} γ Δ t N M =
  Σ[ Δ₁ ∈ Ctx ] Σ[ w₁ ∈ Ren [] (Δ₁ ⟨ ρ ⟩) (toCtx St ++ᶜ Δ) ]
  Σ[ V₁ ∈ Δ₁ ⊢V⦂ [ ρ ] A ]
    (unbox-tgt w₁ V₁ ≡ env-cell γ Δ t)
  × (N ≐ᶜ unbox w₁ V₁ (env-Cˢ γ (Δ ∷ A) M))

env-eternal-C-unbox : ∀ {Δ Γc Δ₀ A C ρ} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                    → (w : Ren [] (Δ₀ ⟨ ρ ⟩) (Δ ++ᶜ Γc)) → (V : Δ₀ ⊢V⦂ [ ρ ] A)
                    → (M : ((Δ ++ᶜ Γc) ∷ A) ⊢C⦂ C)
                    → (t : Tgt (Δ ++ᶜ Γc) ([ ρ ] A)) → unbox-tgt w V ≡ t
                    → (rel : proj₁ t ≾ᵣ ρ)
                    → Σ[ Δ₁ ∈ Ctx ] Σ[ w₁ ∈ Ren [] (Δ₁ ⟨ ρ ⟩) Γc ]
                      Σ[ V₁ ∈ Δ₁ ⊢V⦂ [ ρ ] A ]
                        (unbox-tgt w₁ V₁ ≡ env-eternal-cell lf η t)
                      × (env-eternal-C lf η (unbox w V M)
                         ≐ᶜ unbox w₁ V₁ (env-eternal-C lf η M))

env-eternal-C-unbox {[]} {Γc} {A = A} lf-[] η w V M .(unbox-tgt w V) refl rel =
    _ , castʳ (++ᶜ-identityˡ {Γc}) w , V
  , unbox-tgt-castʳ (++ᶜ-identityˡ {Γc}) w V
  , ≐ᶜ-trans (≡→≐ᶜ (cast-unbox (++ᶜ-identityˡ {Γc})))
      (unbox-≐ refl
        (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) (++ᶜ-identityˡ {Γc}))
                         (++ᶜ-identityˡ {Γc ∷ A}) M)))

env-eternal-C-unbox {Δ ∷ B} {Γc} {A = A} (lf-∷ lf) η w V M
                    .(unbox-tgt w V) refl rel
  with env-eternal-C-unbox lf (λ x → η (Tl-∷ x))
         (castʳ (castOf {Δ} {B} Γc) (unbox-var-ren (proj₂ tE) relE))
         (var (λ _ → ≾ᵣ-refl) Hd)
         (castᶜ (castOf {Δ} {B} (Γc ∷ A)) (M [ Tl-∷ (bvar B Γc) ↦ W₀ ]c))
         _
         (trans (unbox-tgt-castʳ (castOf {Δ} {B} Γc)
                                  (unbox-var-ren (proj₂ tE) relE)
                                  (var (λ _ → ≾ᵣ-refl) Hd))
                (cong (Tgt-cast (castOf {Δ} {B} Γc))
                      (unbox-var-tgt (proj₂ tE) relE)))
         relE
  where
    W₀   = bval Γc (V-rename (empty-ren lf) (η Hd))
    tE   = rvar-tgt (proj₂ (unbox-tgt w V)) (bvar B Γc) W₀
    relE = ≾ᵣ-trans (proj₂ (proj₂ (⟨ proj₂ (unbox-tgt w V) ⟩[ bvar B Γc
                                     ↦ W₀ ]rvar))) rel
... | Δ₁ , w₁ , V₁ , ce , eq =
    Δ₁ , w₁ , V₁ , ce
  , ≐ᶜ-trans
      (env-eternal-C-≐ lf (λ x → η (Tl-∷ x))
        (≐ᶜ-trans
          (castᶜ-≐ (castOf {Δ} {B} Γc)
            (sub-unbox w V M (bvar B Γc)
                       (bval Γc (V-rename (empty-ren lf) (η Hd))) _))
          (≐ᶜ-trans
            (≡→≐ᶜ (cast-unbox (castOf {Δ} {B} Γc)))
            (unbox-≐ refl
              (≡→≐ᶜ (castᶜ-irr
                       (cong (_∷ A) (castOf {Δ} {B} Γc))
                       (castOf {Δ} {B} (Γc ∷ A)) _))))))
      eq

env-Cˢ-unbox : ∀ {St Γ Δ₀ A C ρ} → (γ : Env St Γ) → (Δ : Ctx)
             → (w : Ren [] (Δ₀ ⟨ ρ ⟩) (Γ ++ᶜ Δ)) → (V : Δ₀ ⊢V⦂ [ ρ ] A)
             → (M : ((Γ ++ᶜ Δ) ∷ A) ⊢C⦂ C)
             → (t : Tgt (Γ ++ᶜ Δ) ([ ρ ] A)) → unbox-tgt w V ≡ t
             → (rel : proj₁ t ≾ᵣ ρ)
             → UnboxAt γ Δ t (env-Cˢ γ Δ (unbox w V M)) M

env-Cˢ-unbox ⌊ St ⌋ Δ w V M .(unbox-tgt w V) refl rel =
  _ , w , V , refl , ≐ᶜ-refl _

env-Cˢ-unbox (∅ᵉ St) Δ w V M .(unbox-tgt w V) refl rel =
    _ , (cong-ren (∅-ren St) ∘ʳ w) , V
  , unbox-tgt-∘ (cong-ren (∅-ren St)) w V , ≐ᶜ-refl _

env-Cˢ-unbox (sliceᵉ γ q) Δ w V M .(unbox-tgt w V) refl rel
  with env-Cˢ-unbox γ Δ w V M _ refl rel
... | Δ₁ , w₁ , V₁ , ce , eq =
    Δ₁ , (cong-ren (slice-renᵘ q) ∘ʳ w₁) , V₁
  , trans (unbox-tgt-∘ (cong-ren (slice-renᵘ q)) w₁ V₁)
          (cong (var-tgt′ (cong-ren (slice-renᵘ q))) ce)
  , C-rename-cong (cong-ren (slice-renᵘ q)) eq

env-Cˢ-unbox {A = A} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ w V M
             .(unbox-tgt w V) refl rel
  with env-Cˢ-unbox γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
         (castʳ (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) w) V
         (castᶜ (cong (_∷ A) (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ)) M)
         _ (unbox-tgt-castʳ (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) w V) rel
... | Δ₁ , w₁ , V₁ , ce , eq =
    Δ₁ , (cong-ren (unbox-ren q) ∘ʳ castʳ eOut w₁) , V₁
  , trans (unbox-tgt-∘ (cong-ren (unbox-ren q)) (castʳ eOut w₁) V₁)
          (cong (var-tgt′ (cong-ren (unbox-ren q)))
                (trans (unbox-tgt-castʳ eOut w₁ V₁) (cong (Tgt-cast eOut) ce)))
  , ≐ᶜ-trans
      (C-rename-cong (cong-ren (unbox-ren q))
        (castᶜ-≐ eOut
          (≐ᶜ-trans (env-Cˢ-≐ γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
                       (≡→≐ᶜ (cast-unbox (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ)))) eq)))
      (≐ᶜ-trans
        (≡→≐ᶜ (cong (C-rename (cong-ren (unbox-ren q))) (cast-unbox eOut)))
        (unbox-≐ refl
          (C-rename-cong (cong-ren (unbox-ren q))
            (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) eOut)
                     (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) (Δ ∷ A))) _)))))
  where
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ)

env-Cˢ-unbox {A = A} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V₀ γ) Δ w V M
             .(unbox-tgt w V) refl rel
  with env-Cˢ-unbox γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
         (castʳ (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) w) V
         (castᶜ (cong (_∷ A) (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ)) M)
         _ (unbox-tgt-castʳ (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) w V) rel
... | Δ₁ , w₁ , V₁ , ce , eq =
    Δ₁ , castʳ eOut w₁ , V₁
  , trans (unbox-tgt-castʳ eOut w₁ V₁) (cong (Tgt-cast eOut) ce)
  , ≐ᶜ-trans
      (castᶜ-≐ eOut
        (≐ᶜ-trans (env-Cˢ-≐ γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
                     (≡→≐ᶜ (cast-unbox (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ)))) eq))
      (≐ᶜ-trans (≡→≐ᶜ (cast-unbox eOut))
        (unbox-≐ refl
          (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) eOut)
                   (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ₀ ] A₀) (Δ ∷ A))) _))))
  where
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ₀ ] A₀) Δ)

env-Cˢ-unbox (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ w V M .(unbox-tgt w V) refl rel
  with env-eternal-C-unbox lf η (castʳ (++ᶜ-assoc Δ₀ Γ₁ Δ) w) V
         (castᶜ (cong (_∷ _) (++ᶜ-assoc Δ₀ Γ₁ Δ)) M)
         _ (unbox-tgt-castʳ (++ᶜ-assoc Δ₀ Γ₁ Δ) w V) rel
... | Δ₁ , w₁ , V₁ , ce , eq
  with env-Cˢ-unbox γ Δ w₁ V₁ _ _ ce
         (env-eternal-cell-rel lf η (Tgt-cast (++ᶜ-assoc Δ₀ Γ₁ Δ)
                                       (unbox-tgt w V)) rel)
...  | Δ₂ , w₂ , V₂ , ce₂ , eq₂ =
    Δ₂ , w₂ , V₂ , ce₂
  , ≐ᶜ-trans
      (env-Cˢ-≐ γ Δ
        (≐ᶜ-trans
          (env-eternal-C-≐ lf η
            (≡→≐ᶜ (cast-unbox (++ᶜ-assoc Δ₀ Γ₁ Δ))))
          eq))
      (≐ᶜ-trans eq₂
        (unbox-≐ refl
          (env-Cˢ-≐ γ (Δ ∷ _)
            (env-eternal-C-≐ lf η
              (≡→≐ᶜ (castᶜ-irr (cong (_∷ _) (++ᶜ-assoc Δ₀ Γ₁ Δ))
                       (++ᶜ-assoc Δ₀ Γ₁ (Δ ∷ _)) _))))))

env-Cˢ-unbox {A = A} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ w V M
             .(unbox-tgt w V) refl rel
  with env-Cˢ-unbox γ ([] ∷ A₀ ++ᶜ Δ)
         (castʳ (++ᶜ-assoc Γ ([] ∷ A₀) Δ) w) V
         (castᶜ (cong (_∷ A) (++ᶜ-assoc Γ ([] ∷ A₀) Δ)) M)
         _ (unbox-tgt-castʳ (++ᶜ-assoc Γ ([] ∷ A₀) Δ) w V) rel
... | Δ₁ , w₁ , V₁ , ce , eq =
    _ , castʳ cOf (unbox-var-ren z relSub) , var (λ _ → ≾ᵣ-refl) Hd
  , trans (unbox-tgt-castʳ cOf (unbox-var-ren z relSub)
                            (var (λ _ → ≾ᵣ-refl) Hd))
          (cong (Tgt-cast cOf)
            (trans (unbox-var-tgt z relSub)
                   (cong (λ u → rvar-tgt (proj₂ u) (bvar A₀ Δ) (bval Δ W))
                         ceOut)))
  , ≐ᶜ-trans
      (castᶜ-≐ cOf
        (≐ᶜ-trans
          (sub-≐ᶜ (bvar A₀ Δ) (≐ᵛ-refl (bval Δ W))
            (≐ᶜ-trans
              (castᶜ-≐ eOut
                (≐ᶜ-trans
                  (env-Cˢ-≐ γ ([] ∷ A₀ ++ᶜ Δ)
                    (≡→≐ᶜ (cast-unbox (++ᶜ-assoc Γ ([] ∷ A₀) Δ))))
                  eq))
              (≡→≐ᶜ (cast-unbox eOut))))
          (sub-unbox (castʳ eOut w₁) V₁ _ (bvar A₀ Δ) (bval Δ W) relSub)))
      (≐ᶜ-trans (≡→≐ᶜ (cast-unbox cOf))
        (unbox-≐ refl
          (≐ᶜ-trans
            (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) cOf)
                     (castOf {toCtx St} {A₀} (Δ ∷ A)) _))
            (castᶜ-≐ (castOf {toCtx St} {A₀} (Δ ∷ A))
              (sub-≐ᶜ (bvar A₀ (Δ ∷ A))
                (≡→≐ᵛ (castᵛ-irr _ _ W))
                (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) eOut)
                         (sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ∷ A)))
                         _)))))))
  where
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    cOf  = castOf {toCtx St} {A₀} Δ

    ceOut = trans (unbox-tgt-castʳ eOut w₁ V₁) (cong (Tgt-cast eOut) ce)

    relSub =
      ≾ᵣ-trans
        (proj₂ (proj₂ (⟨ proj₂ (unbox-tgt (castʳ eOut w₁) V₁) ⟩[ bvar A₀ Δ
                         ↦ bval Δ W ]rvar)))
        (subst (_≾ᵣ _) (sym (cong proj₁ ceOut))
          (env-cell-rel γ ([] ∷ A₀ ++ᶜ Δ)
            (Tgt-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) (unbox-tgt w V)) rel))

    z = proj₂ (rvar-tgt (proj₂ (unbox-tgt (castʳ eOut w₁) V₁))
                        (bvar A₀ Δ) (bval Δ W))

------------------------------------------------------------------------
-- THE CELL ACTION, SUFFIX-FREE
--
-- `env-cell` recurses through *growing* suffixes, so a statement that only
-- makes sense at the empty one — such as "the cell's content is reducible",
-- whose `lookup-body` needs the cell to land in `toCtx St` — cannot be proved
-- against it by induction on the environment. This is the same action read
-- off the environment's zones directly, where the recursion stays at the
-- boundary and every case is a variable of `toCtx St`.
--
-- Two zones are discharged rather than computed. `∅ᵉ` has no variables; and an
-- eternal prefix has no *cell*, because the value it would substitute is a
-- closed one of box type, hence a variable of `[]` (`grad-typ⇒var`).
------------------------------------------------------------------------

env-cell₀ : ∀ {St Γ A ρ} → (γ : Env St Γ)
          → Tgt Γ ([ ρ ] A) → Tgt (toCtx St) ([ ρ ] A)

-- a cell cannot come from an eternal prefix
eternal-no-cell : ∀ {Δ₀ A ρ σ} → (η : ClosedVals Δ₀)
                → [ ρ ] A ∈[ σ ] Δ₀ → ⊥
eternal-no-cell η x =
  not-in-empty-ctx (proj₁ (proj₂ (grad-typ⇒var (η x))))

env-cell₀ ⌊ St ⌋      t         = t
env-cell₀ (∅ᵉ St)     (σ , x)   = ⊥-elim (not-in-empty-ctx x)
env-cell₀ (sliceᵉ γ q) t        = var-tgt′ (slice-renᵘ q) (env-cell₀ γ t)

env-cell₀ (_⟨_⟩ᵉ {ρ = ρ₀} γ q) (σ , Tl-⟨⟩ y) =
  var-tgt′ (unbox-ren q) (Tgt-⟨⟩ ρ₀ (env-cell₀ γ (_ , y)))

env-cell₀ (γ ∷ᵉ W) (σ , Hd)     =
  proj₁ (grad-typ⇒var W) , proj₁ (proj₂ (grad-typ⇒var W))
env-cell₀ (γ ∷ᵉ W) (σ , Tl-∷ y) = env-cell₀ γ (σ , y)

env-cell₀ (liftᵉ V γ) (σ , Hd)     = uᵣ , Hd
env-cell₀ (liftᵉ V γ) (σ , Tl-∷ y) = Tgt-∷ (env-cell₀ γ (σ , y))

env-cell₀ (eternalˡ Δ₀ lf η γ) (σ , x)
  with ∈-++ᶜ-split Δ₀ _ x
... | inj₁ (ρ' , y) = ⊥-elim (eternal-no-cell η y)
... | inj₂ y        = env-cell₀ γ (σ , y)

------------------------------------------------------------------------
-- THE CELL THE ENVIRONMENT SENDS A CELL TO IS REDUCIBLE
--
-- This is `Val` at the box type, for `env-cell₀ γ t` — which is what makes the
-- two substituting zones nothing at all: `_∷ᵉ_`'s cell is the value the zone
-- substitutes, and `Rel-Env` already says that value is `Val` at its box type;
-- `liftᵉ`'s is the freshly allocated cell, and `Rel-Env`'s Kripke component is
-- exactly `store-fresh`'s hypothesis. Both were unreachable while `Val` at a
-- box type quantified over a slice rather than over readability.
------------------------------------------------------------------------

env-cell₀-val : ∀ {St Γ A ρ} → (γ : Env St Γ) → Rel-Env γ
              → (t : Tgt Γ ([ ρ ] A))
              → ∀ {St'} → (e : St ≤ₛ St')
              → (rel : proj₁ (≤ₛ-embed e (proj₂ (env-cell₀ γ t))) ≾ᵣ ρ)
              --------------------------------------------------------------
              → Val A St' (lookup-body St' (≤ₛ-embed e (proj₂ (env-cell₀ γ t)))
                                       rel)

env-cell₀-val ⌊ St ⌋   pγ t       e rel = pγ e (proj₂ t) rel
env-cell₀-val (∅ᵉ St)  pγ (σ , x) e rel = ⊥-elim (not-in-empty-ctx x)

env-cell₀-val {A = A} {ρ = ρ} (sliceᵉ γ q) pγ t {St'} e rel =
  Val-≐ᵛ A (≡→≐ᵛ (lookup-body-≡ St' cellEq rel₁ rel))
           (env-cell₀-val γ pγ t (≤ₛ-trans (ext q) e) rel₁)
  where
    c = proj₂ (env-cell₀ γ t)

    cellEq = trans (≤ₛ-embed-∘ (ext q) e c)
                   (sym (cong (λ z → ≤ₛ-embed e (proj₂ z))
                              (slice-renᵘ-tgt q c)))
    rel₁ = subst (_≾ᵣ ρ) (sym (cong proj₁ cellEq)) rel

env-cell₀-val {A = A} {ρ = ρ} (_⟨_⟩ᵉ {ρ = ρ₀} γ q) pγ (σ , Tl-⟨⟩ y) {St'} e rel =
  Val-≐ᵛ A (≡→≐ᵛ (lookup-body-≡ St' cellEq rel₁ rel))
           (env-cell₀-val γ pγ (_ , y) (≤ₛ-trans (ext q) e) rel₁)
  where
    c = proj₂ (env-cell₀ γ (_ , y))

    cellEq = trans (≤ₛ-embed-∘ (ext q) e c)
                   (sym (cong (λ z → ≤ₛ-embed e (proj₂ z))
                              (unbox-ren-tgt q c)))
    rel₁ = subst (_≾ᵣ ρ) (sym (cong proj₁ cellEq)) rel

env-cell₀-val (γ ∷ᵉ W) (pγ , pW) (σ , Hd)     e rel = pW e rel
env-cell₀-val (γ ∷ᵉ W) (pγ , pW) (σ , Tl-∷ y) e rel =
  env-cell₀-val γ pγ (σ , y) e rel

env-cell₀-val (liftᵉ V γ) (pγ , pV) (σ , Hd) e rel =
  store-fresh V pV (λ _ → ≾ᵣ-refl) e rel

env-cell₀-val {A = A} {ρ = ρ} (liftᵉ V γ) (pγ , pV) (σ , Tl-∷ y) {St'} e rel =
  Val-≐ᵛ A (≡→≐ᵛ (lookup-body-≡ St' cellEq rel₁ rel))
           (env-cell₀-val γ pγ (σ , y) (≤ₛ-trans (∷-suc V id-suc) e) rel₁)
  where
    c = proj₂ (env-cell₀ γ (σ , y))

    cellEq = ≤ₛ-embed-∘ (∷-suc V id-suc) e c
    rel₁ = subst (_≾ᵣ ρ) (sym (cong proj₁ cellEq)) rel

env-cell₀-val (eternalˡ Δ₀ lf η γ) (pγ , et) (σ , x) e rel
  with ∈-++ᶜ-split Δ₀ _ x
... | inj₁ (ρ' , y) = ⊥-elim (eternal-no-cell η y)
... | inj₂ y        = env-cell₀-val γ pγ (σ , y) e rel

------------------------------------------------------------------------
-- THE TWO CELL ACTIONS AGREE
--
-- `env-cell` recurses through growing suffixes, `env-cell₀` stays at the
-- boundary. They agree on the cells that matter — those pushed in from the
-- environment's own context — which is all `FL-unbox` reads, the suffix being
-- empty there.
------------------------------------------------------------------------

Tgt-++ᶜˡ : ∀ {Γ A} → (Δ : Ctx) → Tgt Γ A → Tgt (Γ ++ᶜ Δ) A
Tgt-++ᶜˡ Δ (σ , x) = grade-++ᶜˡ σ Δ , ∈-++ᶜˡ Δ x

Tgt-cast-loop : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (t : Tgt Γ' A)
              → Tgt-cast e (Tgt-cast (sym e) t) ≡ t
Tgt-cast-loop refl t = refl

-- A cell that comes from the *suffix* is left where it is: `cong-ren` is the
-- identity on the suffix, and a substituting zone's boundary variable is not a
-- suffix variable, so `⟨_⟩[_↦_]rvar` leaves it alone (`sub-rvar-r`). This is
-- what the `Hd` halves of `_∷ᵉ_`/`liftᵉ` below need, the boundary entry being
-- a suffix cell at the suffix the zone recurses at.

-- Substituting *at* a resource variable, rather than past it: the counterpart
-- of `sub-rvar-r`, and what the `Hd` halves of `_∷ᵉ_`/`liftᵉ` need. The value
-- put in the variable's place is of box type, hence a variable itself, and the
-- result is that variable pushed back under the suffix.

rvar-hit : ∀ {Γ A ρ} → (Θ : Ctx)
         → (W : split-l (bvar {Γ} ([ ρ ] A) Θ) ⊢V⦂ [ ρ ] A)
         → rvar-tgt (bvar {Γ} ([ ρ ] A) Θ) (bvar {Γ} ([ ρ ] A) Θ) W
         ≡ Tgt-++ᶜˡ (split-r (bvar {Γ} ([ ρ ] A) Θ)) (val-cell W)

rvar-hit []        W = refl
rvar-hit (Θ ∷ C)   W = cong Tgt-∷ (rvar-hit Θ W)
rvar-hit (Θ ⟨ ρ' ⟩) W = cong (Tgt-⟨⟩ ρ') (rvar-hit Θ W)

-- A transport of a concatenation acts on the cell by its prefix half and on
-- the push by its suffix half — which is what `castOf`, being a `cong₂`, is.

Tgt-cast-++ᶜˡ : ∀ {Γ₁ Γ₂ A} → (e₁ : Γ₁ ≡ Γ₂) → {Θ₁ Θ₂ : Ctx} → (e₂ : Θ₁ ≡ Θ₂)
              → (t : Tgt Γ₁ A)
              → Tgt-cast (cong₂ _++ᶜ_ e₁ e₂) (Tgt-++ᶜˡ Θ₁ t)
              ≡ Tgt-++ᶜˡ Θ₂ (Tgt-cast e₁ t)
Tgt-cast-++ᶜˡ refl refl t = refl

-- The cell a box-typed value names travels with a transport of its context.

val-cell-cast : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ') → (W : Γ ⊢V⦂ [ ρ ] A)
              → val-cell (castᵛ e W) ≡ Tgt-cast e (val-cell W)
val-cell-cast refl W = refl

∈-++ᶜʳ-assoc⁻ : ∀ {A ρ} → (Γ Γ' : Ctx) → {Δ : Ctx} → (x : A ∈[ ρ ] Δ)
              → subst (λ Γ₀ → A ∈[ ρ ] Γ₀) (sym (++ᶜ-assoc Γ Γ' Δ))
                      (∈-++ᶜʳ {Γ = Γ} (∈-++ᶜʳ {Γ = Γ'} x))
              ≡ ∈-++ᶜʳ {Γ = Γ ++ᶜ Γ'} x
∈-++ᶜʳ-assoc⁻ Γ Γ' {Δ} x =
  trans (cong (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) (sym (++ᶜ-assoc Γ Γ' Δ)))
              (sym (∈-++ᶜʳ-assoc Γ Γ' x)))
        (subst-sym-subst′ (++ᶜ-assoc Γ Γ' Δ) (∈-++ᶜʳ x))

env-eternal-cell-suffix : ∀ {Δ₀ Γc A ρ σ} → (lf : Lock-free Δ₀)
                        → (η : ClosedVals Δ₀) → (z : [ ρ ] A ∈[ σ ] Γc)
                        → env-eternal-cell lf η (σ , ∈-++ᶜʳ {Γ = Δ₀} z)
                        ≡ (σ , z)

env-eternal-cell-suffix lf-[] η z =
  cong (λ v → _ , v) (∈-++ᶜʳ-[] z)
env-eternal-cell-suffix {Δ ∷ B} {Γc} (lf-∷ lf) η z =
  trans (cong (env-eternal-cell lf (λ x → η (Tl-∷ x)))
              (sub-rvar-r Γc z (bval Γc (V-rename (empty-ren lf) (η Hd)))))
        (env-eternal-cell-suffix lf (λ x → η (Tl-∷ x)) z)

env-cell-suffix : ∀ {St Γ A ρ σ} → (γ : Env St Γ) → (Δ : Ctx)
                → (z : [ ρ ] A ∈[ σ ] Δ)
                → env-cell γ Δ (σ , ∈-++ᶜʳ {Γ = Γ} z)
                ≡ (σ , ∈-++ᶜʳ {Γ = toCtx St} z)

env-cell-suffix ⌊ St ⌋  Δ z = refl
env-cell-suffix (∅ᵉ St) Δ z = cong-ren-tgt-r (∅-ren St) z
env-cell-suffix (sliceᵉ γ q) Δ z =
  trans (cong (var-tgt′ (cong-ren (slice-renᵘ q))) (env-cell-suffix γ Δ z))
        (cong-ren-tgt-r (slice-renᵘ q) z)

env-cell-suffix (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ z =
  trans (cong (λ v → var-tgt′ (cong-ren (unbox-ren q))
                       (Tgt-cast eOut (env-cell γ Δ' (_ , v))))
              (∈-++ᶜʳ-assoc Γ ([] ⟨ ρ₀ ⟩) z))
    (trans (cong (λ v → var-tgt′ (cong-ren (unbox-ren q)) (Tgt-cast eOut v))
                 (env-cell-suffix γ Δ' (∈-++ᶜʳ {Γ = [] ⟨ ρ₀ ⟩} z)))
      (trans (cong (λ v → var-tgt′ (cong-ren (unbox-ren q)) (_ , v))
                   (∈-++ᶜʳ-assoc⁻ (toCtx St) ([] ⟨ ρ₀ ⟩) z))
             (cong-ren-tgt-r (unbox-ren q) z)))
  where
    Δ'   = [] ⟨ ρ₀ ⟩ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ)

env-cell-suffix (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ z =
  trans (cong (λ v → Tgt-cast eOut (env-cell γ Δ' (_ , v)))
              (∈-++ᶜʳ-assoc Γ ([] ∷ [ ρ₀ ] A₀) z))
    (trans (cong (Tgt-cast eOut)
                 (env-cell-suffix γ Δ' (∈-++ᶜʳ {Γ = [] ∷ [ ρ₀ ] A₀} z)))
           (cong (λ v → _ , v) (∈-++ᶜʳ-assoc⁻ (toCtx St) ([] ∷ [ ρ₀ ] A₀) z)))
  where
    Δ'   = [] ∷ [ ρ₀ ] A₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ₀ ] A₀) Δ)

env-cell-suffix (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ z =
  trans (cong (λ v → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                       (rvar-tgt (proj₂ (Tgt-cast eOut (env-cell γ Δ' (_ , v))))
                                 (bvar A₀ Δ) (bval Δ W)))
              (∈-++ᶜʳ-assoc Γ ([] ∷ A₀) z))
    (trans (cong (λ v → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                          (rvar-tgt (proj₂ (Tgt-cast eOut v))
                                    (bvar A₀ Δ) (bval Δ W)))
                 (env-cell-suffix γ Δ' (∈-++ᶜʳ {Γ = [] ∷ A₀} z)))
      (trans (cong (λ v → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                            (rvar-tgt v (bvar A₀ Δ) (bval Δ W)))
                   (∈-++ᶜʳ-assoc⁻ (toCtx St) ([] ∷ A₀) z))
             (sub-rvar-r Δ z (bval Δ W))))
  where
    Δ'   = [] ∷ A₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)

env-cell-suffix (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ z =
  trans (cong (λ v → env-cell γ Δ (env-eternal-cell lf η (_ , v)))
              (∈-++ᶜʳ-assoc Δ₀ Γ₁ z))
    (trans (cong (env-cell γ Δ)
                 (env-eternal-cell-suffix lf η (∈-++ᶜʳ {Γ = Γ₁} z)))
           (env-cell-suffix γ Δ z))

env-cell-push : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx)
              → (t : Tgt Γ ([ ρ ] A))
              → env-cell γ Δ (Tgt-++ᶜˡ Δ t) ≡ Tgt-++ᶜˡ Δ (env-cell₀ γ t)

env-cell-push ⌊ St ⌋  Δ t       = refl
env-cell-push (∅ᵉ St) Δ (σ , x) = ⊥-elim (not-in-empty-ctx x)

env-cell-push (sliceᵉ γ q) Δ t =
  trans (cong (var-tgt′ (cong-ren (slice-renᵘ q))) (env-cell-push γ Δ t))
        (cong-ren-tgt-l (slice-renᵘ q) Δ (proj₂ (env-cell₀ γ t)))

-- The two zones that grow the suffix by a binder split on the variable. A
-- `Tl-∷` is the `⟨⟩ᵉ` pattern with `[] ∷ A₀` for `[] ⟨ ρ₀ ⟩`; a `Hd` is the
-- zone's own boundary variable, which `∈-++ᶜˡ-++ᶜʳ` recognises as a *suffix*
-- variable of the grown suffix, so `env-cell-suffix` carries it across. At
-- `_∷ᵉ_` the substitution then hits it (`split→∈-∈-++ᶜˡ` identifies the pushed
-- boundary variable with `bvar`, and `rvar-hit` reads off the substituted
-- value's own cell); at `liftᵉ` nothing substitutes and it stays the fresh
-- cell. The eternal zone has no cell of its own at all.

env-cell-push (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ (σ , Tl-⟨⟩ y) =
  trans (cong (λ z → var-tgt′ (cong-ren (unbox-ren q))
                       (Tgt-cast eOut (env-cell γ Δ' z)))
              step-in)
    (trans (cong (λ z → var-tgt′ (cong-ren (unbox-ren q)) (Tgt-cast eOut z))
                 (env-cell-push γ Δ' (_ , y)))
      (trans (cong (var-tgt′ (cong-ren (unbox-ren q)))
                   (∈-++ᶜˡ-assoc {Γ = toCtx St} ([] ⟨ ρ₀ ⟩) Δ
                                 (proj₂ (env-cell₀ γ (_ , y)))))
             (cong-ren-tgt-l (unbox-ren q) Δ
                             (proj₂ (Tgt-⟨⟩ ρ₀ (env-cell₀ γ (_ , y)))))))
  where
    Δ'   = [] ⟨ ρ₀ ⟩ ++ᶜ Δ
    eIn  = ++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ)

    -- `Tl-⟨⟩ y` *is* the push of `y` under `[] ⟨ ρ₀ ⟩`, so the zone's
    -- associativity cast just re-brackets the two pushes
    step-in : Tgt-cast eIn (Tgt-++ᶜˡ Δ (σ , Tl-⟨⟩ y))
            ≡ Tgt-++ᶜˡ Δ' (_ , y)
    step-in =
      trans (cong (Tgt-cast eIn)
                  (sym (∈-++ᶜˡ-assoc {Γ = Γ} ([] ⟨ ρ₀ ⟩) Δ y)))
            (Tgt-cast-loop eIn (Tgt-++ᶜˡ Δ' (_ , y)))
env-cell-push (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ (σ , Tl-∷ y) =
  trans (cong (λ z → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                       (rvar-tgt (proj₂ (Tgt-cast eOut (env-cell γ Δ' z)))
                                 (bvar A₀ Δ) (bval Δ W)))
              step-in)
    (trans (cong (λ z → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                          (rvar-tgt (proj₂ (Tgt-cast eOut z))
                                    (bvar A₀ Δ) (bval Δ W)))
                 (env-cell-push γ Δ' (σ , y)))
      (trans (cong (λ z → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                            (rvar-tgt (proj₂ z) (bvar A₀ Δ) (bval Δ W)))
                   (∈-++ᶜˡ-assoc {Γ = toCtx St} ([] ∷ A₀) Δ c))
             (sub-rvar-l Δ c (bval Δ W))))
  where
    Δ'   = [] ∷ A₀ ++ᶜ Δ
    eIn  = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)

    c = proj₂ (env-cell₀ γ (σ , y))

    step-in : Tgt-cast eIn (Tgt-++ᶜˡ Δ (σ , Tl-∷ y)) ≡ Tgt-++ᶜˡ Δ' (σ , y)
    step-in =
      trans (cong (Tgt-cast eIn) (sym (∈-++ᶜˡ-assoc {Γ = Γ} ([] ∷ A₀) Δ y)))
            (Tgt-cast-loop eIn (Tgt-++ᶜˡ Δ' (σ , y)))

env-cell-push (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ (σ , Hd) =
  trans (cong (λ z → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                       (rvar-tgt (proj₂ (Tgt-cast eOut (env-cell γ Δ' z)))
                                 (bvar A₀ Δ) (bval Δ W)))
              (∈-++ᶜˡ-++ᶜʳ Γ ([] ∷ A₀) Δ Hd))
    (trans (cong (λ z → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                          (rvar-tgt (proj₂ (Tgt-cast eOut z))
                                    (bvar A₀ Δ) (bval Δ W)))
                 (env-cell-suffix γ Δ' bnd))
      (trans (cong (λ z → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                            (rvar-tgt (proj₂ z) (bvar A₀ Δ) (bval Δ W)))
                   (trans step-out (sym (split→∈-∈-++ᶜˡ (toCtx St) A₀ Δ))))
        (trans (cong (Tgt-cast (castOf {toCtx St} {A₀} Δ))
                     (rvar-hit Δ (bval Δ W)))
               fin)))
  where
    Δ'   = [] ∷ A₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)

    bnd = ∈-++ᶜˡ {Γ = [] ∷ A₀} Δ Hd

    -- the boundary variable, come across, is `Hd` pushed under the suffix
    step-out : Tgt-cast eOut (grade-++ᶜˡ uᵣ Δ , ∈-++ᶜʳ {Γ = toCtx St} bnd)
             ≡ Tgt-++ᶜˡ Δ (uᵣ , Hd {Γ = toCtx St})
    step-out =
      Tgt-cast-flip (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ) _ _
                    (∈-++ᶜˡ-++ᶜʳ (toCtx St) ([] ∷ A₀) Δ Hd)

    -- `bval` transports the value into `split-l`; `castOf` transports it back
    fin : Tgt-cast (castOf {toCtx St} {A₀} Δ)
            (Tgt-++ᶜˡ (split-r (bvar {toCtx St} A₀ Δ)) (val-cell (bval Δ W)))
        ≡ Tgt-++ᶜˡ Δ (val-cell W)
    fin =
      trans (Tgt-cast-++ᶜˡ (split→∈-split-l (split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}))
                           (split→∈-split-r (split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}))
                           (val-cell (bval Δ W)))
            (cong (Tgt-++ᶜˡ Δ)
              (trans (cong (Tgt-cast (split→∈-split-l
                                        (split-≡-++ᶜ {toCtx St ∷ A₀} {Δ})))
                           (val-cell-cast (sym (split→∈-split-l
                                        (split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}))) W))
                     (Tgt-cast-loop (split→∈-split-l
                                      (split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}))
                                    (val-cell W))))

env-cell-push (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ (σ , Tl-∷ y) =
  trans (cong (λ z → Tgt-cast eOut (env-cell γ Δ' z)) step-in)
    (trans (cong (Tgt-cast eOut) (env-cell-push γ Δ' (σ , y)))
           (∈-++ᶜˡ-assoc {Γ = toCtx St} B₀ Δ (proj₂ (env-cell₀ γ (σ , y)))))
  where
    B₀   = [] ∷ [ ρ₀ ] A₀
    Δ'   = B₀ ++ᶜ Δ
    eIn  = ++ᶜ-assoc Γ B₀ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) B₀ Δ)

    step-in : Tgt-cast eIn (Tgt-++ᶜˡ Δ (σ , Tl-∷ y)) ≡ Tgt-++ᶜˡ Δ' (σ , y)
    step-in =
      trans (cong (Tgt-cast eIn) (sym (∈-++ᶜˡ-assoc {Γ = Γ} B₀ Δ y)))
            (Tgt-cast-loop eIn (Tgt-++ᶜˡ Δ' (σ , y)))

env-cell-push (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ (σ , Hd) =
  trans (cong (λ z → Tgt-cast eOut (env-cell γ Δ' z))
              (∈-++ᶜˡ-++ᶜʳ Γ B₀ Δ Hd))
    (trans (cong (Tgt-cast eOut) (env-cell-suffix γ Δ' bnd))
           (Tgt-cast-flip (++ᶜ-assoc (toCtx St) B₀ Δ) _ _
                          (∈-++ᶜˡ-++ᶜʳ (toCtx St) B₀ Δ Hd)))
  where
    B₀   = [] ∷ [ ρ₀ ] A₀
    Δ'   = B₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) B₀ Δ)

    bnd = ∈-++ᶜˡ {Γ = B₀} Δ Hd

env-cell-push (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ (σ , x)
  with ∈-++ᶜ-split Δ₀ Γ₁ x in eq

... | inj₁ (ρ' , y) = ⊥-elim (eternal-no-cell η y)

... | inj₂ y =
  trans (cong (λ z → env-cell γ Δ
                       (env-eternal-cell lf η
                         (Tgt-cast (++ᶜ-assoc Δ₀ Γ₁ Δ) (Tgt-++ᶜˡ Δ (σ , z)))))
              (∈-++ᶜ-split-inj₂ Δ₀ Γ₁ x y eq))
    (trans (cong (λ z → env-cell γ Δ (env-eternal-cell lf η z))
                 (∈-++ᶜˡ-++ᶜʳ Δ₀ Γ₁ Δ y))
      (trans (cong (env-cell γ Δ)
                   (env-eternal-cell-suffix lf η (∈-++ᶜˡ {Γ = Γ₁} Δ y)))
             (env-cell-push γ Δ (σ , y))))
