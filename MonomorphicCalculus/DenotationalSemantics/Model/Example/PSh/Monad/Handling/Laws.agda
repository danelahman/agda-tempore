------------------------------------------------------------------------
-- Effect handling: the η / delay / op / sub-effecting algebra laws.    --
------------------------------------------------------------------------

{-# OPTIONS --lossy-unification #-}

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base as B
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Laws
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import Data.Product using (_,_; proj₁; proj₂)

open import Util.Equality

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops
open World Wld
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base Grades Wld
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future Grades Wld
open GroundTypes GTy
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Core S Wld GTy
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Effects S Wld GTy

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open Category PShCat using (mapˣᵐ; map⇒ᵐ; exp-strᵐ; fstᵐ; sndᵐ; ⟨_,_⟩ᵐ; curryᵐ; appᵐ)

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Past Grades Wld using (PShPast)
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Adjunction Grades Wld using (PShAdj)
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
  PShCat (GradeSystem.RGrade Grades) PShFut PShPast PShAdj

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Core S Wld GTy

-- The three algebra laws (up to `_≈ᵗ_`): each side folds to the same tree
-- (returning / re-delaying / applying the clause to the rebuilt box).

T-alg-of-handlerᵀ-ηᵀ : ∀ {P A ε'} → (bc : Eternalᵒ P) → (h : Handlerˢ P A)
                     → T-alg-of-handlerᵀ bc h ∘ᵖ mapˣᵐ idᵖ (ηᵀ {Tᵒ A ε'})
                     ≈ᵖ T-≤ (≃ₑ⇒≿ₑ (·ₑ-identityˡ ε')) ∘ᵖ sndᵐ
T-alg-of-handlerᵀ-ηᵀ bc h x = ≈ᵗ-refl _

T-alg-of-handlerᵀ-delayᵀ : ∀ {P A ε' ε''} → (τ : 𝔻) → (bc : Eternalᵒ P) → (h : Handlerˢ P A)
                         → T-alg-of-handlerᵀ bc h ∘ᵖ mapˣᵐ idᵖ (delayᵀ {Tᵒ A ε''} {ε'} τ)
                         ≈ᵖ T-≤ (≃ₑ⇒≿ₑ (·ₑ-assoc (of-durᵉ τ) ε' ε''))
                           ∘ᵖ delayᵀ τ
                           ∘ᵖ [ of-durʳ τ ]ᶠ (T-alg-of-handlerᵀ bc h)
                           ∘ᵖ []-monoidal
                           ∘ᵖ mapˣᵐ (Eternalᵒ.necᵉ bc {of-durʳ τ}) idᵖ
T-alg-of-handlerᵀ-delayᵀ {P = P} τ bc h (pv , boxT) =
  sub-congᵗ
    (delay-≈ (λ q → T-alg-of-handlerˢ-congᵖ bc h
                      (≈-sym P (Eternalᵒ.necᵉ-≤ bc (≃ᵣ⇒≾ᵣ map-of-durᵉ) pv q))
                      (fun boxT (⊑-mono (≃ᵣ⇒≾ᵣ map-of-durᵉ) q))))

T-alg-of-handlerᵀ-≤ : ∀ {P A ε₁ ε₂ ε'} → (bc : Eternalᵒ P) → (h : Handlerˢ P A) → (p : ε₁ ≾ₑ ε₂)
                    → T-alg-of-handlerᵀ {P} {A} {ε₂} {ε'} bc h ∘ᵖ mapˣᵐ idᵖ (T-≤ p)
                    ≈ᵖ T-≤ (·ₑ-monoˡ-≾ₑ p) ∘ᵖ T-alg-of-handlerᵀ {P} {A} {ε₁} {ε'} bc h
T-alg-of-handlerᵀ-≤ bc h p x = ≈ᵗ-refl _

T-alg-of-handlerᵀ-opᵀ : ∀ {P A ε' ε''} → (op : Op) → (bc : Eternalᵒ P) → (h : Handlerˢ P A)
                      → T-alg-of-handlerᵀ bc h ∘ᵖ mapˣᵐ idᵖ (opᵀ {Tᵒ A ε''} {ε'} op)
                      ≈ᵖ T-≤ (≃ₑ⇒≿ₑ (·ₑ-assoc (op-grade op) ε' ε''))
                        ∘ᵖ clause h op (ε' ·ₑ ε'')
                        ∘ᵖ ⟨ fstᵐ
                           , ⟨ fstᵐ ∘ᵖ sndᵐ
                             ,   [ mapᵉ (op-grade op) ]ᶠ
                                   (curryᵐ (T-alg-of-handlerᵀ bc h
                                     ∘ᵖ ⟨ fstᵐ ∘ᵖ fstᵐ
                                        , appᵐ ∘ᵖ ⟨ sndᵐ ∘ᵖ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ))
                               ∘ᵖ []-monoidal
                               ∘ᵖ mapˣᵐ (Eternalᵒ.necᵉ bc {mapᵉ (op-grade op)}) idᵖ
                               ∘ᵖ ⟨ fstᵐ , sndᵐ ∘ᵖ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
T-alg-of-handlerᵀ-opᵀ {P = P} op bc h (pv , (v , boxk)) =
  sub-congᵗ
    (app-cong (clause h op _)
      (≈-refl P ,
       (≈-refl ⟦ param op ⟧ᵍ ,
        (λ q p y → T-alg-of-handlerˢ-cong bc h
                     (fun-nat (app (Eternalᵒ.necᵉ bc) pv) q p)
                     (fun-nat boxk q p ⊑-refl y)))))

-- The fold is a congruence in the *handler*: pointwise-equal clauses fold to
-- equal algebras. By induction on the tree — the only handler-dependent node is
-- `op`, where the matching clause is applied (`heq`) and the folded continuations
-- agree by the inductive hypothesis.

{-# TERMINATING #-}
T-alg-of-handlerˢ-congʰ : ∀ {P A ε ε' w} (bc : Eternalᵒ P) {h h' : Handlerˢ P A}
                          (heq : ∀ op ε'' → clause h op ε'' ≈ᵖ clause h' op ε'')
                          (pv : carrier P w) (t : Tˢ (Tᵒ A ε') ε w)
                        → T-alg-of-handlerˢ bc h pv t ≈ᵗ T-alg-of-handlerˢ bc h' pv t
T-alg-of-handlerˢ-congʰ bc heq pv (leaf s) = ≈ᵗ-refl _
T-alg-of-handlerˢ-congʰ {P = P} bc {h = h} {h' = h'} heq pv (op-node op v k kc kn) =
  sub-congᵗ
    (≈ᵗ-trans (heq op _ (pv , (v , handler-box bc pv h op k kc kn)))
              (app-cong (clause h' op _)
                (≈-refl P ,
                 (≈-refl ⟦ param op ⟧ᵍ ,
                  (λ q r y → T-alg-of-handlerˢ-congʰ bc heq
                               (fun (app (Eternalᵒ.necᵉ bc) pv) (⊑ρ∘ᵘ q r))
                               (k (⊑ρ∘ᵘ q r) y))))))
T-alg-of-handlerˢ-congʰ bc heq pv (delay-node τ k kn) =
  sub-congᵗ
    (delay-≈ (λ q → T-alg-of-handlerˢ-congʰ bc heq
                      (fun (app (Eternalᵒ.necᵉ bc) pv) q) (k q)))
T-alg-of-handlerˢ-congʰ bc heq pv (sub p t) =
  sub-≈ (T-alg-of-handlerˢ-congʰ bc heq pv t)

T-alg-of-handlerᵀ-cong : ∀ {P A ε ε'} (bc : Eternalᵒ P) {h h' : Handlerˢ P A}
                       → (∀ op ε'' → clause h op ε'' ≈ᵖ clause h' op ε'')
                       → T-alg-of-handlerᵀ {P} {A} {ε} {ε'} bc h
                       ≈ᵖ T-alg-of-handlerᵀ {P} {A} {ε} {ε'} bc h'
T-alg-of-handlerᵀ-cong bc heq (pv , t) = T-alg-of-handlerˢ-congʰ bc heq pv t

-- Naturality in the eternal parameter: reindexing the handler's clauses along a
-- `necᵉ`-commuting coalgebra morphism `f` equals reindexing the fold's parameter.
-- By induction on the tree; at each `op`/`delay` node the continuation's parameter
-- is advanced by `necᵉ`, and `f` commuting with `necᵉ` (`fcomm`) closes the case.

-- Reindexing a handler's parameter along `f`. The clauses are precomposed, and
-- ambivalence transports directly: precomposition only replaces the eternal
-- parameter `pv'` by `app f pv'`, leaving the boxes it relates untouched.

reindexʰ : ∀ {P P' A} → (f : P' →ᵖ P) → Handlerˢ P A → Handlerˢ P' A
reindexʰ f h =
    (λ op ε'' → clause h op ε'' ∘ᵖ mapˣᵐ f idᵖ)
  , (λ op q x → clause-mono′ h op q (app f (proj₁ x) , proj₂ x))

{-# TERMINATING #-}
T-alg-of-handlerˢ-natᴾ : ∀ {P P' A ε ε' w} (bc : Eternalᵒ P) (bc' : Eternalᵒ P')
                         (f : P' →ᵖ P)
                         (fcomm : ∀ {ρ} → [ ρ ]ᶠ f ∘ᵖ Eternalᵒ.necᵉ bc' {ρ}
                                          ≈ᵖ Eternalᵒ.necᵉ bc {ρ} ∘ᵖ f)
                         (h : Handlerˢ P A)
                         (pv' : carrier P' w) (t : Tˢ (Tᵒ A ε') ε w)
                       → T-alg-of-handlerˢ bc' (reindexʰ f h) pv' t
                       ≈ᵗ T-alg-of-handlerˢ bc h (app f pv') t
T-alg-of-handlerˢ-natᴾ bc bc' f fcomm h pv' (leaf s) = ≈ᵗ-refl _
T-alg-of-handlerˢ-natᴾ {P = P} bc bc' f fcomm h pv' (op-node op v k kc kn) =
  sub-congᵗ
    (app-cong (clause h op _)
      (≈-refl P ,
       (≈-refl ⟦ param op ⟧ᵍ ,
        (λ q r y → ≈ᵗ-trans
          (T-alg-of-handlerˢ-natᴾ bc bc' f fcomm h
             (fun (app (Eternalᵒ.necᵉ bc') pv') (⊑ρ∘ᵘ q r)) (k (⊑ρ∘ᵘ q r) y))
          (T-alg-of-handlerˢ-congᵖ bc h (fcomm pv' (⊑ρ∘ᵘ q r)) (k (⊑ρ∘ᵘ q r) y))))))
T-alg-of-handlerˢ-natᴾ bc bc' f fcomm h pv' (delay-node τ k kn) =
  sub-congᵗ
    (delay-≈ (λ q → ≈ᵗ-trans
      (T-alg-of-handlerˢ-natᴾ bc bc' f fcomm h (fun (app (Eternalᵒ.necᵉ bc') pv') q) (k q))
      (T-alg-of-handlerˢ-congᵖ bc h (fcomm pv' q) (k q))))
T-alg-of-handlerˢ-natᴾ bc bc' f fcomm h pv' (sub p t) =
  sub-≈ (T-alg-of-handlerˢ-natᴾ bc bc' f fcomm h pv' t)

T-alg-of-handlerᵀ-natᴾ : ∀ {P P' A ε ε'} (bc : Eternalᵒ P) (bc' : Eternalᵒ P')
                         (f : P' →ᵖ P)
                       → (∀ {ρ} → [ ρ ]ᶠ f ∘ᵖ Eternalᵒ.necᵉ bc' {ρ}
                                  ≈ᵖ Eternalᵒ.necᵉ bc {ρ} ∘ᵖ f)
                       → (h : Handlerˢ P A)
                       → T-alg-of-handlerᵀ {P'} {A} {ε} {ε'} bc' (reindexʰ f h)
                       ≈ᵖ T-alg-of-handlerᵀ {P} {A} {ε} {ε'} bc h ∘ᵖ mapˣᵐ f idᵖ
T-alg-of-handlerᵀ-natᴾ bc bc' f fcomm h (pv' , t) =
  T-alg-of-handlerˢ-natᴾ bc bc' f fcomm h pv' t

-- The same, stated for an arbitrary handler `h'` whose clauses are the
-- reindexed ones. This is the form consumers have (a renamed or substituted
-- handler comes with a clause-level equation, not as a literal `reindexʰ`), and
-- it is insensitive to which ambivalence proof `h'` happens to carry.

T-alg-of-handlerᵀ-natᴾ′ : ∀ {P P' A ε ε'} (bc : Eternalᵒ P) (bc' : Eternalᵒ P')
                          (f : P' →ᵖ P)
                        → (∀ {ρ} → [ ρ ]ᶠ f ∘ᵖ Eternalᵒ.necᵉ bc' {ρ}
                                   ≈ᵖ Eternalᵒ.necᵉ bc {ρ} ∘ᵖ f)
                        → (h : Handlerˢ P A) → (h' : Handlerˢ P' A)
                        → (∀ op ε'' → clause h' op ε'' ≈ᵖ clause h op ε'' ∘ᵖ mapˣᵐ f idᵖ)
                        → T-alg-of-handlerᵀ {P'} {A} {ε} {ε'} bc' h'
                        ≈ᵖ T-alg-of-handlerᵀ {P} {A} {ε} {ε'} bc h ∘ᵖ mapˣᵐ f idᵖ
T-alg-of-handlerᵀ-natᴾ′ {P} {P'} {A} {ε} {ε'} bc bc' f fcomm h h' ceq x =
  ≈ᵗ-trans
    (T-alg-of-handlerᵀ-cong {P'} {A} {ε} {ε'} bc' {h = h'} {h' = reindexʰ f h} ceq x)
    (T-alg-of-handlerᵀ-natᴾ {P} {P'} {A} {ε} {ε'} bc bc' f fcomm h x)

-- Sub-effecting in the *inner* grade. The handler must be *ambivalent* in the
-- residual grade (`Monoˢ`); the fold selects `h op` by that grade, so at an
-- `op`-node the coerced continuation is folded by the *higher-grade* clause,
-- and `clause-mono` moves the coercion back out (`·ₑ-monoʳ`) so it may be
-- shared with the other cases. Leaves / delays / subs commute the coercion
-- through the `sub`/`ε-subst` machinery (`sub-ε-substᵗ`, `sub-delay`, `sub-∘`).

{-# TERMINATING #-}
T-alg-of-handlerˢ-≤ⁱ : ∀ {P A ε ε₁' ε₂' w} (bc : Eternalᵒ P) (h : Handlerˢ P A)
                       (p : ε₁' ≾ₑ ε₂')
                       (pv : carrier P w) (t : Tˢ (Tᵒ A ε₁') ε w)
                     → T-alg-of-handlerˢ {ε' = ε₂'} bc h pv (Tˢᶠ (T-≤ p) t)
                     ≈ᵗ sub (·ₑ-monoʳ-≾ₑ p) (T-alg-of-handlerˢ {ε' = ε₁'} bc h pv t)
T-alg-of-handlerˢ-≤ⁱ {ε₁' = ε₁'} {ε₂' = ε₂'} bc h p pv (leaf s) =
  sub-swapᵗ _ _ _ _ s
-- the clause's own ambivalence moves the coercion out of the operation, with
-- the inductive hypothesis supplying its relatedness premise on the two boxes
T-alg-of-handlerˢ-≤ⁱ {ε₁' = ε₁'} {ε₂' = ε₂'} bc h p pv (op-node {ε = ε₀} op v k kc kn) =
  ≈ᵗ-trans
    (sub-congᵗ
      (clause-mono h op (·ₑ-monoʳ-≾ₑ p) pv v
         (handler-box bc pv h op k kc kn) _
         (λ r s y → T-alg-of-handlerˢ-≤ⁱ bc h p
                      (fun (app (Eternalᵒ.necᵉ bc) pv) (⊑ρ∘ᵘ r s)) (k (⊑ρ∘ᵘ r s) y))))
    (sub-swapᵗ _ _ _ _ _)
T-alg-of-handlerˢ-≤ⁱ {ε₁' = ε₁'} {ε₂' = ε₂'} bc h p pv (delay-node {ε = ε₀} τ k kn) =
  ≈ᵗ-trans
    (sub-congᵗ
      (delay-≈ (λ q → T-alg-of-handlerˢ-≤ⁱ bc h p
                        (fun (app (Eternalᵒ.necᵉ bc) pv) q) (k q))))
    (≈ᵗ-trans
      (sub-congᵗ
        (≈ᵗ-sym (sub-delayᵗ (·ₑ-monoʳ-≾ₑ p) _ _)))
      (sub-swapᵗ _ _ _ _ _))
T-alg-of-handlerˢ-≤ⁱ bc h p pv (sub p₀ t) =
  ≈ᵗ-trans (sub-≈ (T-alg-of-handlerˢ-≤ⁱ bc h p pv t))
           (≈ᵗ-trans (sub-∘ᵗ _ (·ₑ-monoˡ-≾ₑ p₀)
                            (≾ₑ-trans (·ₑ-monoʳ-≾ₑ p) (·ₑ-monoˡ-≾ₑ p₀)) _)
                     (≈ᵗ-sym (sub-∘ᵗ _ _
                            (≾ₑ-trans (·ₑ-monoʳ-≾ₑ p) (·ₑ-monoˡ-≾ₑ p₀)) _)))

T-alg-of-handlerᵀ-≤ⁱ : ∀ {P A ε ε₁' ε₂'} (bc : Eternalᵒ P) (h : Handlerˢ P A)
                       (p : ε₁' ≾ₑ ε₂')
                     → T-alg-of-handlerᵀ {P} {A} {ε} {ε₂'} bc h ∘ᵖ mapˣᵐ idᵖ (Tᶠ (T-≤ p))
                     ≈ᵖ T-≤ (·ₑ-monoʳ-≾ₑ p) ∘ᵖ T-alg-of-handlerᵀ {P} {A} {ε} {ε₁'} bc h
T-alg-of-handlerᵀ-≤ⁱ bc h p (pv , t) =
  T-alg-of-handlerˢ-≤ⁱ bc h p pv t
