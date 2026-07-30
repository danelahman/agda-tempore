------------------------------------------------------------------------
-- The commutation theorem itself.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality
module Syntax.Substitutions.Renaming.Core (Spec : LanguageSpec) where
open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.RenActions    Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import Syntax.Renamings.Equivalence    Spec
open import Syntax.Renamings.Coherence      Spec
open import Syntax.Terms.Equivalence        Spec
open import Syntax.Terms.Transport          Spec
open import Syntax.Substitutions.Equivalence Spec
open import Syntax.Substitutions.Variables   Spec
open import Syntax.Substitutions.Weakening   Spec
open import Syntax.Substitutions.Renaming.Variables Spec
open import Syntax.Substitutions.Renaming.Clauses Spec

-- RENAMING THE PREFIX COMMUTES WITH SUBSTITUTING AT THE VARIABLE PAST IT
--
-- Mutual induction on the term, at an arbitrary suffix, as `sub-wk`: each
-- binding former grows the suffix, `cong-ren {Θ ∷ A} r` *is*
-- `cong-∷-ren (cong-ren {Θ} r)` and the substituted variable at `Θ ∷ A` *is*
-- `Tl-∷` of the one at `Θ`, both definitionally. What is left per case is
-- pushing the two casts through the former.

mutual

  ren-sub-V : ∀ {Γ Γ' B} → (r : Ren [] Γ' Γ) → (Θ : Ctx) → ∀ {A}
            → (U : ((Γ ∷ B) ++ᶜ Θ) ⊢V⦂ A) → (W : Γ ⊢V⦂ B)
            → V-rename (cong-ren {Γ'' = Θ} r)
                (castᵛ (castOf {Γ} {B} Θ)
                  (U [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                       ↦ castᵛ (sym (split→∈-split-l
                                       (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]v))
            ≡ castᵛ (castOf {Γ'} {B} Θ)
                 ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) U)
                    [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                      ↦ castᵛ (sym (split→∈-split-l
                                      (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                              (V-rename r W) ]v)

  ren-sub-V {Γ} {Γ'} {B} r Θ (var f y) W = ren-sub-var r Θ y W f f

  ren-sub-V {Γ} {Γ'} {B} r Θ (const c) W =
    trans ((cong (V-rename (cong-ren {Γ'' = Θ} r))
                         (cast-const (castOf {Γ} {B} Θ))))
             ((sym (cast-const (castOf {Γ'} {B} Θ))))

  ren-sub-V {Γ} {Γ'} {B} r Θ ⋆ W =
    trans ((cong (V-rename (cong-ren {Γ'' = Θ} r))
                         (cast-⋆ (castOf {Γ} {B} Θ))))
             ((sym (cast-⋆ (castOf {Γ'} {B} Θ))))

  ren-sub-V {Γ} {Γ'} {B} r Θ ⦉ V₁ , V₂ ⦊ W =
    trans ((cong (V-rename (cong-ren {Γ'' = Θ} r))
                         (cast-pair (castOf {Γ} {B} Θ))))
      (trans (cong₂ ⦉_,_⦊ (ren-sub-V r Θ V₁ W) (ren-sub-V r Θ V₂ W))
                ((sym (cast-pair (castOf {Γ'} {B} Θ)))))

  ren-sub-V {Γ} {Γ'} {B} r Θ {A = A ⇒ C} (lam M) W =
    trans ((cong (V-rename (cong-ren {Γ'' = Θ} r))
                         (cast-lam (castOf {Γ} {B} Θ) _)))
      (trans
        (cong lam (trans
                 ((cong (C-rename (cong-ren {Γ'' = Θ ∷ A} r))
                             (castᶜ-irr (cong (_∷ A) (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ∷ A)) _)))
                 (trans (ren-sub-C r (Θ ∷ A) M W)
                           ((castᶜ-irr (castOf {Γ'} {B} (Θ ∷ A))
                                            (cong (_∷ A) (castOf {Γ'} {B} Θ)) _)))))
        ((sym (cast-lam (castOf {Γ'} {B} Θ) _))))

  ren-sub-C : ∀ {Γ Γ' B} → (r : Ren [] Γ' Γ) → (Θ : Ctx) → ∀ {C}
            → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ C) → (W : Γ ⊢V⦂ B)
            → C-rename (cong-ren {Γ'' = Θ} r)
                (castᶜ (castOf {Γ} {B} Θ)
                  (M [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                       ↦ castᵛ (sym (split→∈-split-l
                                       (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]c))
            ≡ castᶜ (castOf {Γ'} {B} Θ)
                 ((C-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) M)
                    [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                      ↦ castᵛ (sym (split→∈-split-l
                                      (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                              (V-rename r W) ]c)

  ren-sub-C {Γ} {Γ'} {B} r Θ (return V) W =
    trans ((cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-ret (castOf {Γ} {B} Θ))))
      (trans (cong return (ren-sub-V r Θ V W))
                ((sym (cast-ret (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (_⨟_ {A = A} {ε = ε} M N) W =
    trans ((cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-seq (castOf {Γ} {B} Θ))))
      (trans
        (cong₂ _⨟_ (ren-sub-C r Θ M W)
               (trans
                 ((cong (C-rename (cong-ren {Γ'' = Θ ⟨ mapᵉ ε ⟩ ∷ A} r))
                             (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                              (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _)))
                 (trans (ren-sub-C r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
                           ((castᶜ-irr
                                    (castOf {Γ'} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A))
                                    (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                          (castOf {Γ'} {B} Θ)) _)))))
        ((sym (cast-seq (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (V₁ · V₂) W =
    trans ((cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-app (castOf {Γ} {B} Θ))))
      (trans (cong₂ _·_ (ren-sub-V r Θ V₁ W) (ren-sub-V r Θ V₂ W))
                ((sym (cast-app (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (match_`in_ {A = A} {B = B'} V N) W =
    trans ((cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-match (castOf {Γ} {B} Θ))))
      (trans
        (cong₂ match_`in_ (ren-sub-V r Θ V W)
                 (trans
                   ((cong (C-rename (cong-ren {Γ'' = Θ ∷ A ∷ B'} r))
                               (castᶜ-irr (cong (λ Γ₀ → Γ₀ ∷ A ∷ B')
                                                (castOf {Γ} {B} Θ))
                                          (castOf {Γ} {B} (Θ ∷ A ∷ B')) _)))
                   (trans (ren-sub-C r (Θ ∷ A ∷ B') N W)
                             ((castᶜ-irr (castOf {Γ'} {B} (Θ ∷ A ∷ B'))
                                              (cong (λ Γ₀ → Γ₀ ∷ A ∷ B')
                                                    (castOf {Γ'} {B} Θ)) _)))))
        ((sym (cast-match (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (absurd V) W =
    trans ((cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-absurd (castOf {Γ} {B} Θ))))
      (trans (cong absurd (ren-sub-V r Θ V W))
                ((sym (cast-absurd (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (perform op V M) W =
    trans ((cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-perform (castOf {Γ} {B} Θ))))
      (trans
        (cong₂ (perform _) (ren-sub-V r Θ V W)
                   (trans
                     ((cong (C-rename (cong-ren {Γ'' = Θ'} r))
                                 (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                                            ∷ type-of-gtype (arity op))
                                                  (castOf {Γ} {B} Θ))
                                            (castOf {Γ} {B} Θ') _)))
                     (trans (ren-sub-C r Θ' M W)
                               ((castᶜ-irr
                                        (castOf {Γ'} {B} Θ')
                                        (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                                        ∷ type-of-gtype (arity op))
                                              (castOf {Γ'} {B} Θ)) _)))))
        ((sym (cast-perform (castOf {Γ'} {B} Θ)))))
    where
      Θ' = Θ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)

  ren-sub-C {Γ} {Γ'} {B} r Θ (delay τ M) W =
    trans ((cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-delay (castOf {Γ} {B} Θ))))
      (trans
        (cong (delay _) (trans
                   ((cong (C-rename (cong-ren {Γ'' = Θ ⟨ of-natʳ τ ⟩} r))
                               (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) (castOf {Γ} {B} Θ))
                                          (castOf {Γ} {B} (Θ ⟨ of-natʳ τ ⟩)) _)))
                   (trans (ren-sub-C r (Θ ⟨ of-natʳ τ ⟩) M W)
                             ((castᶜ-irr (castOf {Γ'} {B} (Θ ⟨ of-natʳ τ ⟩))
                                              (cong (_⟨ of-natʳ τ ⟩)
                                                    (castOf {Γ'} {B} Θ)) _)))))
        ((sym (cast-delay (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (box {A = A} {ρ = ρ} V M) W =
    trans ((cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-box (castOf {Γ} {B} Θ))))
      (trans
        (cong₂ box (trans
                 ((cong (V-rename (cong-ren {Γ'' = Θ ⟨ ρ ⟩} r))
                             (castᵛ-irr (cong (_⟨ ρ ⟩) (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ⟨ ρ ⟩)) _)))
                 (trans (ren-sub-V r (Θ ⟨ ρ ⟩) V W)
                           ((castᵛ-irr (castOf {Γ'} {B} (Θ ⟨ ρ ⟩))
                                            (cong (_⟨ ρ ⟩) (castOf {Γ'} {B} Θ)) _))))
               (trans
                 ((cong (C-rename (cong-ren {Γ'' = Θ ∷ [ ρ ] A} r))
                             (castᶜ-irr (cong (_∷ [ ρ ] A) (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ∷ [ ρ ] A)) _)))
                 (trans (ren-sub-C r (Θ ∷ [ ρ ] A) M W)
                           ((castᶜ-irr (castOf {Γ'} {B} (Θ ∷ [ ρ ] A))
                                            (cong (_∷ [ ρ ] A)
                                                  (castOf {Γ'} {B} Θ)) _)))))
        ((sym (cast-box (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (coerce p M) W =
    trans ((cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-coerce (castOf {Γ} {B} Θ))))
      (trans (coerce-≡ (ren-sub-C r Θ M W))
                ((sym (cast-coerce (castOf {Γ'} {B} Θ)))))

  -- the clause hypothesis is the recursion at the canonical restricted
  -- contexts, threaded through `ren-sub-C-cast` so it runs on the bare clause
  ren-sub-C {Γ} {Γ'} {B} r Θ (handle_`with_`in {A = A} {B = B'} {ε = ε} M H N) W =
    ren-sub-handle r Θ M H N W
      (ren-sub-C r Θ M W)
      (ren-sub-C r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
      (λ et op ε'' →
         ren-sub-C-cast (restrict-ren {Ξ = []} r) (Θ ᴱ ++ᶜ Dcl B' op ε'')
                        (ren-sub-eTot {Γ} {B} Θ et (Dcl B' op ε''))
                        (H op ε'') (eternal-val-restrict et W))
  ren-sub-C r Θ (unbox {A = A} w V M)    W =
    ren-sub-unbox r Θ w V M W (ren-sub-C r (Θ ∷ A) M W)

  -- `ren-sub-C` with its context given by an equation, so the `handle` clause
  -- can recurse on the bare clause term (as `sub-wk-C-cast`).

  ren-sub-C-cast : ∀ {Γ Γ' B Γ₀} → (r : Ren [] Γ' Γ) → (Θ : Ctx)
                 → ∀ {C} → (e : Γ₀ ≡ (Γ ∷ B) ++ᶜ Θ) → (M : Γ₀ ⊢C⦂ C)
                 → (W : Γ ⊢V⦂ B)
                 → RenSubC r Θ (subst (_⊢C⦂ C) e M) W

  ren-sub-C-cast r Θ refl M W = ren-sub-C r Θ M W

