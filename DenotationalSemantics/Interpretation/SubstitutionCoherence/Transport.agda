------------------------------------------------------------------------
-- Context-equality transports, and clause retyping.
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad
module DenotationalSemantics.Interpretation.SubstitutionCoherence.Transport
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S
open import Syntax.Substitutions S
open import Syntax.Renamings.Equivalence S using (eternal?-no)

open Category Cat
open Future Fut
open Past Pst
open Adjunction Adj
open GroundTypes GTy
open GroundEternal GE
open Monad Mon

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Base S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Unbox S Cat Fut Pst Adj GTy Mon GE

-- Interpreting a context-equality transport of a computation: the transport
-- becomes the corresponding equality renaming (both are the identity when the
-- equality is `refl`). Used to strip the `subst`s that `_[_↦_]c` inserts in the
-- handler clauses.

-- Retyping a clause along a context equality preserves parametricity.

substᴾᶜ : ∀ {Δ Δ' D C} → (e : Δ ≡ Δ') → (t : Δ ++ᶜ D ⊢C⦂ C)
        → Paramᶜ t → Paramᶜ (subst (λ Γ₀ → Γ₀ ++ᶜ D ⊢C⦂ C) e t)
substᴾᶜ refl t p = p

substᴾᶜ′ : ∀ {Δ Δ' C} → {e : Δ ≡ Δ'} → (t : Δ ⊢C⦂ C)
         → Paramᶜ t → Paramᶜ (subst (_⊢C⦂ C) e t)
substᴾᶜ′ {e = refl} t p = p

substᴾᵛ : ∀ {Δ Δ' A} → {e : Δ ≡ Δ'} → (t : Δ ⊢V⦂ A)
        → Paramᵛ t → Paramᵛ (subst (_⊢V⦂ A) e t)
substᴾᵛ {e = refl} t p = p

subst-ctx-interp : ∀ {Δ Δ' C} → (e : Δ ≡ Δ') → (t : Δ ⊢C⦂ C) → (p : Paramᶜ t)
                 → ⟦ subst (_⊢C⦂ C) e t ⟧ᶜᵗ (substᴾᶜ′ {e = e} t p)
                 ≈ᵐ ⟦ t ⟧ᶜᵗ p ∘ᵐ ⟦ eq-ren e ⟧ʳ
subst-ctx-interp refl t p = ≈ᵐ-sym (∘ᵐ-identityʳ _)

subst-val-interp : ∀ {Δ Δ' A} → (e : Δ ≡ Δ') → (t : Δ ⊢V⦂ A) → (p : Paramᵛ t)
                 → ⟦ subst (_⊢V⦂ A) e t ⟧ᵛᵗ (substᴾᵛ {e = e} t p)
                 ≈ᵐ ⟦ t ⟧ᵛᵗ p ∘ᵐ ⟦ eq-ren e ⟧ʳ
subst-val-interp refl t p = ≈ᵐ-sym (∘ᵐ-identityʳ _)

subst-clause-interp : ∀ {Δ Δ' D C} → (e : Δ ≡ Δ') → (t : Δ ++ᶜ D ⊢C⦂ C)
                    → (p : Paramᶜ t)
                    → ⟦ subst (λ Γ₀ → Γ₀ ++ᶜ D ⊢C⦂ C) e t ⟧ᶜᵗ (substᴾᶜ e t p)
                    ≈ᵐ ⟦ t ⟧ᶜᵗ p ∘ᵐ ⟦ eq-ren (cong (_++ᶜ D) e) ⟧ʳ
subst-clause-interp refl t p = ≈ᵐ-sym (∘ᵐ-identityʳ _)

-- The interpretation of an equality renaming depends only on the endpoints of
-- the context equality (UIP), so any two proofs give the same transport.

-- Context extension is injective, so an equality between two contexts sharing
-- their last two entries restricts to their ambient parts.

ctx-∷-inj : ∀ {Δ Δ' A} → Δ ∷ A ≡ Δ' ∷ A → Δ ≡ Δ'
ctx-∷-inj refl = refl

-- Hence such a retyping is a nested product reindexing whose inner component
-- depends only on the ambient parts — in particular not on the residual grade
-- carried by the last entry.

eq-ren-∷∷ : ∀ {Δ Δ' pt kt} → (e : (Δ ∷ pt) ∷ kt ≡ (Δ' ∷ pt) ∷ kt)
          → ⟦ eq-ren e ⟧ʳ
          ≈ᵐ mapˣᵐ (mapˣᵐ ⟦ eq-ren (ctx-∷-inj (ctx-∷-inj e)) ⟧ʳ idᵐ) idᵐ
eq-ren-∷∷ {pt = pt} {kt = kt} e =
  ≈ᵐ-trans (eq-ren-irr e (cong (_∷ kt) (cong (_∷ pt) (ctx-∷-inj (ctx-∷-inj e)))))
  (≈ᵐ-trans (eq-ren-∷ (cong (_∷ pt) (ctx-∷-inj (ctx-∷-inj e))))
            (mapˣᵐ-cong (eq-ren-∷ (ctx-∷-inj (ctx-∷-inj e))) ≈ᵐ-refl))

-- A clause-context retyping is a nested product reindexing, and in particular
-- acts only on the ambient part — it is independent of the residual grade the
-- continuation slot carries.

eq-ren-clause : ∀ {Δ Δ'} → (e : Δ ≡ Δ') → (Γ' : Ctx) → (pt kt : VType)
              → ⟦ eq-ren (cong (_++ᶜ (Γ' ∷ pt ∷ kt)) e) ⟧ʳ
              ≈ᵐ mapˣᵐ (mapˣᵐ ⟦ eq-ren (cong (_++ᶜ Γ') e) ⟧ʳ idᵐ) idᵐ
eq-ren-clause e Γ' pt kt =
  ≈ᵐ-trans (eq-ren-irr (cong (_++ᶜ (Γ' ∷ pt ∷ kt)) e)
                       (cong (_∷ kt) (cong (_∷ pt) (cong (_++ᶜ Γ') e))))
  (≈ᵐ-trans (eq-ren-∷ (cong (_∷ pt) (cong (_++ᶜ Γ') e)))
            (mapˣᵐ-cong (eq-ren-∷ (cong (_++ᶜ Γ') e)) ≈ᵐ-refl))


-- Retyping a clause family's ambient context preserves the clauses' uniformity
-- in the residual grade: the retyping acts on the ambient context only, so it
-- commutes with the continuation's coercion (`mapˣ-swapᵐ`), after which the
-- original uniformity applies.

subst-clauses-uniform :
  ∀ {Δ Δ' B} → (e : Δ ≡ Δ')
  → (H : (op : Op) → (ε'' : E)
       → Δ ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
  → (∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'')
       → ⟦ H op ε₂'' ⟧ᶜᵗ (pH op ε₂'')
           ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
       ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H op ε₁'' ⟧ᶜᵗ (pH op ε₁''))
  → (∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'')
       → ⟦ subst (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₂'')
                          ⊢C⦂ B ‼ (op-grade op ·ₑ ε₂''))
                 e (H op ε₂'') ⟧ᶜᵗ (substᴾᶜ e (H op ε₂'') (pH op ε₂''))
           ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
       ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q)
           ∘ᵐ ⟦ subst (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₁'')
                               ⊢C⦂ B ‼ (op-grade op ·ₑ ε₁''))
                      e (H op ε₁'') ⟧ᶜᵗ (substᴾᶜ e (H op ε₁'') (pH op ε₁'')))
subst-clauses-uniform e H pH uH op q =
  ≈ᵐ-trans (∘ᵐ-congˡ (subst-clause-interp e (H op _) (pH op _)))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ
    (≈ᵐ-trans (∘ᵐ-congˡ (eq-ren-clause e [] _ _))
    (≈ᵐ-trans (mapˣ-swapᵐ _ _)
              (∘ᵐ-congʳ (≈ᵐ-sym (eq-ren-clause e [] _ _))))))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (uH op q))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
            (∘ᵐ-congʳ (≈ᵐ-sym (subst-clause-interp e (H op _) (pH op _)))))))))

-- Computation lemmas for `eternal?`: with the eternality decision in hand, all
-- the `with eternal?`-defined functions (`_ᴱ`, `∈-ᴱ-split`, `restrict-sub-env`,
-- …) can be forced to reduce by `rewrite`ing their scrutinee — cleaner than
-- per-function unfold lemmas whose signatures are themselves `_ᴱ`-stuck.
-- (`eternal?-yes` is in `Interpretation.Renaming`, which needs it first.)

-- The canonical eternal-skeleton reassociation for the `∈-ᴱ-split` image.
∈-ᴱ-e₀ : ∀ {Γ A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ)
       → split-l (split→∈ (∈-ᴱ-split et x)) ++ᶜ split-r (split→∈ (∈-ᴱ-split et x))
       ≡ (split-l x ++ᶜ split-r x) ᴱ
∈-ᴱ-e₀ et x = trans (cong₂ _++ᶜ_ (split→∈-split-l (∈-ᴱ-split et x))
                                 (split→∈-split-r (∈-ᴱ-split et x)))
                    (sym (ᴱ-++ᶜ (split-l x) (split-r x)))

-- When the substituted variable is not eternal, `restrict-sub-env` is the pure
-- reindexing transport of the (equal) eternal skeletons. Induction on the
-- variable, mirroring `restrict-sub-env`'s `with`-structure; the head is the
-- identity and each `∷`/`⟨⟩` step is `eq-ren-∷`/`eq-ren-irr` bookkeeping.

restrict-transport : ∀ {Γ A ρ} → (¬et : ¬ Eternal A) → (x : A ∈[ ρ ] Γ)
                   → (W : split-l x ⊢V⦂ A) → (e : Γ ᴱ ≡ (split-l x ++ᶜ split-r x) ᴱ)
                   → restrict-sub-env x W ≈ᵐ ⟦ eq-ren e ⟧ʳ
restrict-transport {A = A} ¬et Hd W e with eternal? A
... | yes et = ⊥-elim (¬et et)
... | no  _  = ≈ᵐ-sym (eq-ren-irr e refl)
restrict-transport ¬et (Tl-∷ {Γ = Γ₀} {B = B} x) W e with eternal? B
... | yes _ =
  ≈ᵐ-trans (mapˣᵐ-cong (restrict-transport ¬et x W (ᴱ-drop-split ¬et x)) ≈ᵐ-refl)
  (≈ᵐ-trans (≈ᵐ-sym (eq-ren-∷ (ᴱ-drop-split ¬et x)))
            (eq-ren-irr (cong (_∷ B) (ᴱ-drop-split ¬et x)) e))
... | no  _ = restrict-transport ¬et x W e
restrict-transport ¬et (Tl-⟨⟩ x) W e = restrict-transport ¬et x W e

-- The canonical eternal-skeleton transport for an eternal variable: it
-- reconciles the split point of `∈-ᴱ-split` (via `split→∈-split-l`/`-r`) with
-- the eternal restrictions of the two halves.

canon-e : ∀ {Γ A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ)
        → split-l (split→∈ (∈-ᴱ-split et x)) ++ᶜ split-r (split→∈ (∈-ᴱ-split et x))
          ≡ (split-l x ++ᶜ split-r x) ᴱ
canon-e et x =
  trans (cong₂ _++ᶜ_ (split→∈-split-l (∈-ᴱ-split et x)) (split→∈-split-r (∈-ᴱ-split et x)))
        (sym (ᴱ-++ᶜ (split-l x) (split-r x)))

-- When the substituted variable *is* eternal, its restricted value is placed
-- (via `sub-env` at the split point of `∈-ᴱ-split`) exactly where
-- `restrict-sub-env` inserts it, once the eternal-skeleton transport is
-- accounted for. Induction on the variable; the head uses `eternal-irrelevant`
-- to reconcile the two `Eternal` witnesses.

eternal-bridge-core : ∀ {Γ A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ)
                    → (W : split-l x ⊢V⦂ A)
                    → (e : split-l (split→∈ (∈-ᴱ-split et x)) ++ᶜ split-r (split→∈ (∈-ᴱ-split et x))
                           ≡ (split-l x ++ᶜ split-r x) ᴱ)
                    → sub-env (split→∈ (∈-ᴱ-split et x))
                        (subst (_⊢V⦂ A) (sym (split→∈-split-l (∈-ᴱ-split et x)))
                          (eternal-val-restrict et W))
                        (substᴾᵛ {e = sym (split→∈-split-l (∈-ᴱ-split et x))}
                                 (eternal-val-restrict et W)
                                 (eternal-val-restrictᴾ et W))
                        ∘ᵐ ⟦ eq-ren e ⟧ʳ
                      ≈ᵐ restrict-sub-env x W
eternal-bridge-core {A = A} et Hd W e with eternal? A
... | yes p =
  ≈ᵐ-trans (∘ᵐ-congʳ (eq-ren-irr e refl))
  (≈ᵐ-trans (∘ᵐ-identityʳ _)
            (⟨ ≈ᵐ-refl
             , ≡→≈ᵐ (cong (λ q → ⟦ eternal-val-restrict q W ⟧ᵛᵗ
                                    (eternal-val-restrictᴾ q W))
                          (eternal-irrelevant et p)) ⟩ᵐ-cong))
... | no ¬et = ⊥-elim (¬et et)
eternal-bridge-core et (Tl-∷ {B = B} x) W e with eternal? B
... | yes _ =
  ≈ᵐ-trans (∘ᵐ-congʳ (eq-ren-irr e (cong (_∷ B) (canon-e et x))))
  (≈ᵐ-trans (∘ᵐ-congʳ (eq-ren-∷ (canon-e et x)))
  (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
            (mapˣᵐ-cong (eternal-bridge-core et x W (canon-e et x)) (∘ᵐ-identityˡ _))))
... | no _ = eternal-bridge-core et x W e
eternal-bridge-core et (Tl-⟨⟩ x) W e = eternal-bridge-core et x W e

