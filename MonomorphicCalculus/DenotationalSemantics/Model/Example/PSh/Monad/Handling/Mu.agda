--------------------------------------------------------------------------
-- Effect handling: the algebra (μ) law and its grade-transport lemmas. --
--------------------------------------------------------------------------

{-# OPTIONS --lossy-unification #-}

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base as B
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Mu
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
open Category PShCat using (mapˣᵐ; map⇒ᵐ; exp-strᵐ; fstᵐ; sndᵐ; ⟨_,_⟩ᵐ)

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Past Grades Wld using (PShPast)
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Adjunction Grades Wld using (PShAdj)
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
  PShCat (GradeSystem.RGrade Grades) PShFut PShPast PShAdj

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Handling.Core S Wld GTy

-- A coercion node absorbs a transport on either side (the `sub` witnesses are
-- irrelevant to `_≈ᵗ_`).

sub-ε-substˢ : ∀ {A ε₁ ε₂ ε₃ w} → (e : ε₁ ≡ ε₂) → (q : ε₂ ≾ₑ ε₃) → (q' : ε₁ ≾ₑ ε₃)
             → (t : Tˢ A ε₁ w)
             → sub q (ε-substˢ e t) ≈ᵗ sub q' t
sub-ε-substˢ refl q q' t = sub-≈ (≈ᵗ-refl t)

ε-substˢ-sub' : ∀ {A ε₁ ε₂ ε₃ w} → (q : ε₁ ≾ₑ ε₂) → (e : ε₂ ≡ ε₃) → (q' : ε₁ ≾ₑ ε₃)
              → (t : Tˢ A ε₁ w)
              → ε-substˢ e (sub q t) ≈ᵗ sub q' t
ε-substˢ-sub' q refl q' t = sub-≈ (≈ᵗ-refl t)

-- The handler is uniform in its grade index. The algebra law applies the
-- clause at two grades that are only *propositionally* equal —
-- `(ε₁ ·ₑ ε') ·ₑ ε''` on the left, `ε₁ ·ₑ (ε' ·ₑ ε'')` on the right. A
-- `Handlerˢ` is an arbitrary family indexed by the grade, so those are
-- different morphisms at different types; but they coincide up to
-- transport, which is what the following make precise.

-- Transporting a boxed continuation along an equality of residual grades.

box-ε-substˢ : ∀ {A X ρ ε₁ ε₂ w} → ε₁ ≡ ε₂
             → [ ρ ]ᶜ (X ⇒ᵖ Tᵒ A ε₁) w → [ ρ ]ᶜ (X ⇒ᵖ Tᵒ A ε₂) w
box-ε-substˢ refl b = b

-- Applying the clause at a transported grade is transporting the application.

app-ε-substˢ : ∀ {P A ε₁ ε₂ w} → (h : Handlerˢ P A) → (op : Op) → (e : ε₁ ≡ ε₂)
             → (pv : carrier P w)
             → (v : carrier ⟦ param op ⟧ᵍ w)
             → (b : [ mapᵉ (op-grade op) ]ᶜ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A ε₁) w)
             → app (clause h op ε₁) (pv , (v , b))
             ≈ᵗ ε-substˢ (cong (op-grade op ·ₑ_) (sym e))
                  (app (clause h op ε₂) (pv , (v , box-ε-substˢ e b)))
app-ε-substˢ h op refl pv v b = ≈ᵗ-refl _

-- Reading a transported boxed continuation is transporting what it reads.

box-ε-substˢ-fun : ∀ {A X ρ ε₁ ε₂ w} → (e : ε₁ ≡ ε₂)
                 → (b : [ ρ ]ᶜ (X ⇒ᵖ Tᵒ A ε₁) w)
                 → ∀ {w'} (q : w ⊑[ ρ ] w') {w''} (r : w' ⊑[ uᵣ ] w'')
                 → (y : carrier X w'')
                 → B.fun (F.fun (box-ε-substˢ e b) q) r y
                 ≡ ε-substˢ e (B.fun (F.fun b q) r y)
box-ε-substˢ-fun refl b q r y = refl

-- A grade transport pushes out through a delay node. The transported node's
-- own coherence witness is *constructed* here (rather than taken as an
-- argument), since `_≈ᵗ_` does not determine it.

delay-ε-substˢ-nat : ∀ {A ε₁ ε₂ τ w} → (e : ε₁ ≡ ε₂)
                   → (f : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε₁ w')
                   → (fn : ∀ {w' w''} (q : w ⊑[ mapᵉ (of-durᵉ τ) ] w')
                             (r : w' ⊑[ uᵣ ] w'')
                         → f (⊑ρ∘ᵘ q r) ≈ᵗ transportᵗ r (f q))
                   → ∀ {w' w''} (q : w ⊑[ mapᵉ (of-durᵉ τ) ] w') (r : w' ⊑[ uᵣ ] w'')
                   → ε-substˢ e (f (⊑ρ∘ᵘ q r)) ≈ᵗ transportᵗ r (ε-substˢ e (f q))
delay-ε-substˢ-nat e f fn q r =
  ≈ᵗ-trans (ε-substˢ-congᵗ e (fn q r))
           (≡→≈ᵗ (sym (transportᵗ-ε-substˢ r e (f q))))

delay-ε-substˢ : ∀ {A ε₁ ε₂ τ w} → (e : ε₁ ≡ ε₂)
               → (f : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A ε₁ w')
               → (fn : ∀ {w' w''} (q : w ⊑[ mapᵉ (of-durᵉ τ) ] w') (r : w' ⊑[ uᵣ ] w'')
                     → f (⊑ρ∘ᵘ q r) ≈ᵗ transportᵗ r (f q))
               → delay-node τ (λ q → ε-substˢ e (f q)) (delay-ε-substˢ-nat e f fn)
               ≈ᵗ ε-substˢ (cong (of-durᵉ τ ·ₑ_) e) (delay-node τ f fn)
delay-ε-substˢ refl f fn = delay-≈ (λ q → ≈ᵗ-refl _)

-- Advancing a necessitated parameter under a node (`box▸`) agrees with
-- necessitating the parameter already advanced to the node's world. This is the
-- comultiplication law `necᵉ-δ` (a composite-grade box splits into nested ones).

necᵉ-box▸ : ∀ {P ρ₀ ε₀ w w' w''} (bc : Eternalᵒ P) (pv : carrier P w)
            (q : w ⊑[ mapᵉ ρ₀ ] w') (r : w' ⊑[ mapᵉ ε₀ ] w'')
          → _≈_ P (F.fun (box▸ P q (B.app (Eternalᵒ.necᵉ bc {mapᵉ (ρ₀ ·ₑ ε₀)}) pv)) r)
                  (F.fun (B.app (Eternalᵒ.necᵉ bc {mapᵉ ε₀})
                                (F.fun (B.app (Eternalᵒ.necᵉ bc {mapᵉ ρ₀}) pv) q)) r)
necᵉ-box▸ {P = P} bc pv q r =
  ≈-trans P (Eternalᵒ.necᵉ-≤ bc (≃ᵣ⇒≿ᵣ map-·ᵉ) pv (⊑-trans q r))
            (Eternalᵒ.necᵉ-δ bc pv q r)

-- The fold is an algebra: folding a two-layer tree is folding the outer layer
-- after folding each inner one. By induction on the tree — at each node the
-- fold and the multiplication agree, so the two transports coincide.

T-alg-of-handlerˢ-μˢ : ∀ {P A ε ε' ε'' w} → (bc : Eternalᵒ P) → (h : Handlerˢ P A)
                     → (pv : carrier P w)
                     → (t : Tˢ (Tᵒ (Tᵒ A ε'') ε') ε w)
                     → T-alg-of-handlerˢ {ε = ε ·ₑ ε'} {ε''} bc h pv (μˢ t)
                     ≈ᵗ sub (≃ₑ⇒≿ₑ (·ₑ-assoc ε ε' ε''))
                          (T-alg-of-handlerˢ {ε = ε} {ε' ·ₑ ε''} bc h pv
                            (Tˢᶠ (T-alg-of-handlerᵀ bc h)
                              (strˢ _ (app (Eternalᵒ.necᵉ bc) pv) t)))
T-alg-of-handlerˢ-μˢ {P = P} {ε' = ε'} {ε'' = ε''} bc h pv (leaf t) =
  ≈ᵗ-trans
    (sub-congᵗ (T-alg-of-handlerˢ-congᵖ bc h
                 (≈-sym P (≈-trans P (Eternalᵒ.necᵉ-≤ bc (≃ᵣ⇒≿ᵣ map-uᵉ) pv ⊑-refl)
                                     (≈-trans P (Eternalᵒ.necᵉ-u bc pv ⊑-refl)
                                                (transport-refl P pv))))
                 t))
    (≈ᵗ-sym (sub-∘ᵗ _ _ _ _))
-- The clauses at the two associations of the residual grade are related by
-- the handler's ambivalence (`clause-mono`), the inductive hypothesis
-- supplying its premise on the two boxes.
T-alg-of-handlerˢ-μˢ {P = P} {A = A} {ε' = ε'} {ε'' = ε''} {w = w} bc h pv
                     (op-node {ε = ε₁} op v k kc kn) =
  ≈ᵗ-trans (sub3ᵗ _ _ _ _ _ _)
    (sub-congᵗ (sub-congᵗ
      (≈ᵗ-sym (clause-mono h op (≃ₑ⇒≾ₑ (·ₑ-assoc ε₁ ε' ε'')) pv v BXμ BX' rel))))
  where
    -- the RHS's folded, strength-threaded continuation and its coherences
    cont' : ∀ {w'} → w ⊑[ mapᵉ (op-grade op) ] w' → carrier ⟦ arity op ⟧ᵍ w'
          → Tˢ (Tᵒ A (ε' ·ₑ ε'')) ε₁ w'
    cont' q' y = Tˢᶠ (T-alg-of-handlerᵀ bc h)
                     (strˢ P (box▸ P q' (app (Eternalᵒ.necᵉ bc) pv)) (k q' y))

    kc' : ∀ {w'} (q' : w ⊑[ mapᵉ (op-grade op) ] w') {y y' : carrier ⟦ arity op ⟧ᵍ w'}
        → _≈_ ⟦ arity op ⟧ᵍ y y' → cont' q' y ≈ᵗ cont' q' y'
    kc' q' e = Tˢᶠ-congᵗ (T-alg-of-handlerᵀ bc h) (strˢ-congᵗ P (λ r → ≈-refl P) (kc q' e))

    kn' : ∀ {w' w''} (q' : w ⊑[ mapᵉ (op-grade op) ] w') (r : w' ⊑[ uᵣ ] w'')
          (y : carrier ⟦ arity op ⟧ᵍ w')
        → cont' (⊑ρ∘ᵘ q' r) (transport ⟦ arity op ⟧ᵍ r y) ≈ᵗ transportᵗ r (cont' q' y)
    kn' q' r y =
      ≈ᵗ-trans
        (Tˢᶠ-congᵗ (T-alg-of-handlerᵀ bc h)
          (≈ᵗ-trans
            (strˢ-congᵗ P (λ t → []-fun-irr (app (Eternalᵒ.necᵉ bc) pv) _ _) (kn q' r y))
            (strˢ-natᵗ P (box▸ P q' (app (Eternalᵒ.necᵉ bc) pv)) r (k q' y))))
        (Tˢᶠ-natᵗ (T-alg-of-handlerᵀ bc h) r
          (strˢ P (box▸ P q' (app (Eternalᵒ.necᵉ bc) pv)) (k q' y)))

    BXμ = handler-box bc pv h op (λ q' y → μˢ (k q' y))
            (λ q' e → μˢ-congᵗ (kc q' e))
            (λ q' r y → ≈ᵗ-trans (μˢ-congᵗ (kn q' r y)) (μˢ-natᵗ r (k q' y)))

    BX' = handler-box bc pv h op cont' kc' kn'

    rel : ∀ {w'} (q : w ⊑[ mapᵉ (op-grade op) ] w') {w''} (r : w' ⊑[ uᵣ ] w'')
          (y : carrier ⟦ arity op ⟧ᵍ w'')
        → B.fun (F.fun BX' q) r y ≈ᵗ sub (≃ₑ⇒≾ₑ (·ₑ-assoc ε₁ ε' ε'')) (B.fun (F.fun BXμ q) r y)
    rel q r y =
      ≈ᵗ-sym
        (≈ᵗ-trans
          (sub-congᵗ (T-alg-of-handlerˢ-μˢ bc h (fun (app (Eternalᵒ.necᵉ bc) pv) (⊑ρ∘ᵘ q r))
                                          (k (⊑ρ∘ᵘ q r) y)))
        (≈ᵗ-trans (sub-∘ᵗ _ _ ≾ₑ-refl _)
        (≈ᵗ-trans (sub-uᵗ _ _)
          (T-alg-of-handlerˢ-congᵗ bc h _
            (Tˢᶠ-congᵗ (T-alg-of-handlerᵀ bc h)
              (strˢ-congᵗ P (λ r' → ≈-sym P (necᵉ-box▸ bc pv (⊑ρ∘ᵘ q r) r'))
                          (≈ᵗ-refl (k (⊑ρ∘ᵘ q r) y))))))))
T-alg-of-handlerˢ-μˢ {P = P} {A = A} {ε' = ε'} {ε'' = ε''} {w = w} bc h pv
                     (delay-node {ε = ε₁} τ k kn) =
  ≈ᵗ-trans
    (sub-congᵗ (sub-congᵗ
      (≈ᵗ-trans
        (delay-≈ (λ q →
          ≈ᵗ-trans (T-alg-of-handlerˢ-μˢ bc h (fun (app (Eternalᵒ.necᵉ bc) pv) q) (k q))
                   (sub-congᵗ
                      (T-alg-of-handlerˢ-congᵗ bc h _
                        (Tˢᶠ-congᵗ (T-alg-of-handlerᵀ bc h)
                          (strˢ-congᵗ P (λ r → ≈-sym P (necᵉ-box▸ bc pv q r))
                                      (≈ᵗ-refl (k q))))))))
        (≈ᵗ-sym (sub-delayᵗ (≃ₑ⇒≿ₑ (·ₑ-assoc ε₁ ε' ε'')) f-tgt fn)))))
    (≈ᵗ-sym (sub3ᵗ _ _ _ _ _ _))
  where
    f-tgt : ∀ {w'} → w ⊑[ mapᵉ (of-durᵉ τ) ] w' → Tˢ A (ε₁ ·ₑ (ε' ·ₑ ε'')) w'
    f-tgt q = T-alg-of-handlerˢ bc h (fun (app (Eternalᵒ.necᵉ bc) pv) q)
                (Tˢᶠ (T-alg-of-handlerᵀ bc h)
                  (strˢ P (box▸ P q (app (Eternalᵒ.necᵉ bc) pv)) (k q)))

    fn : ∀ {w' w''} (q : w ⊑[ mapᵉ (of-durᵉ τ) ] w') (r : w' ⊑[ uᵣ ] w'')
       → f-tgt (⊑ρ∘ᵘ q r) ≈ᵗ transportᵗ r (f-tgt q)
    fn q r =
      ≈ᵗ-trans
        (T-alg-of-handlerˢ-congᵖ bc h (fun-nat (app (Eternalᵒ.necᵉ bc) pv) q r)
          (Tˢᶠ (T-alg-of-handlerᵀ bc h)
            (strˢ P (box▸ P (⊑ρ∘ᵘ q r) (app (Eternalᵒ.necᵉ bc) pv)) (k (⊑ρ∘ᵘ q r)))))
      (≈ᵗ-trans
        (T-alg-of-handlerˢ-congᵗ bc h _
          (≈ᵗ-trans
            (Tˢᶠ-congᵗ (T-alg-of-handlerᵀ bc h)
              (≈ᵗ-trans
                (strˢ-congᵗ P (λ t → []-fun-irr (app (Eternalᵒ.necᵉ bc) pv) _ _) (kn q r))
                (strˢ-natᵗ P (box▸ P q (app (Eternalᵒ.necᵉ bc) pv)) r (k q))))
            (Tˢᶠ-natᵗ (T-alg-of-handlerᵀ bc h) r
              (strˢ P (box▸ P q (app (Eternalᵒ.necᵉ bc) pv)) (k q)))))
        (T-alg-of-handlerˢ-nat bc h r (fun (app (Eternalᵒ.necᵉ bc) pv) q)
          (Tˢᶠ (T-alg-of-handlerᵀ bc h)
            (strˢ P (box▸ P q (app (Eternalᵒ.necᵉ bc) pv)) (k q)))))
T-alg-of-handlerˢ-μˢ {P = P} {ε = ε} {ε' = ε'} {ε'' = ε''} bc h pv (sub {ε = ε₀} p t) =
  ≈ᵗ-trans
    (sub-congᵗ (≈ᵗ-trans (T-alg-of-handlerˢ-μˢ bc h pv t)
                     (sub-congᵗ
                        (T-alg-of-handlerˢ-congᵗ bc h pv
                          (Tˢᶠ-congᵗ (T-alg-of-handlerᵀ bc h)
                            (strˢ-congᵗ P
                              (λ q → ≈-sym P (Eternalᵒ.necᵉ-≤ bc (map-monotoneᵉ p) pv q))
                              (≈ᵗ-refl t)))))))
    (sub-swapᵗ _ _ _ _ _)
-- Packaging the two laws as morphism equations.

T-alg-of-handlerᵀ-μᵀ : ∀ {P A ε ε' ε''} → (bc : Eternalᵒ P) → (h : Handlerˢ P A)
                     → T-alg-of-handlerᵀ {P} {A} {ε ·ₑ ε'} {ε''} bc h
                         ∘ᵖ mapˣᵐ idᵖ (μᵀ {Tᵒ A ε''} {ε} {ε'})
                     ≈ᵖ T-≤ (≃ₑ⇒≿ₑ (·ₑ-assoc ε ε' ε''))
                         ∘ᵖ T-alg-of-handlerᵀ {P} {A} {ε} {ε' ·ₑ ε''} bc h
                         ∘ᵖ ⟨ fstᵐ
                            , Tᶠ (T-alg-of-handlerᵀ {P} {A} {ε'} {ε''} bc h)
                              ∘ᵖ strᵀ
                              ∘ᵖ mapˣᵐ (Eternalᵒ.necᵉ bc {mapᵉ ε}) idᵖ ⟩ᵐ
T-alg-of-handlerᵀ-μᵀ bc h (pv , t) = T-alg-of-handlerˢ-μˢ bc h pv t
