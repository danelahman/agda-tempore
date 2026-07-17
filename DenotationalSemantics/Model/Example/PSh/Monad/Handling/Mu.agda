------------------------------------------------------------------------
-- Effect handling: the algebra (μ) law and its grade-transport lemmas. --
------------------------------------------------------------------------

{-# OPTIONS --lossy-unification #-}

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.GroundTypes
import DenotationalSemantics.Model.Example.PSh.Base as B
import DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module DenotationalSemantics.Model.Example.PSh.Monad.Handling.Mu
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)

open import Util.Equality

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops
open World Wld
open import DenotationalSemantics.Model.Example.PSh.Base Grades Wld
open import DenotationalSemantics.Model.Example.PSh.Modality.Future Grades Wld
open GroundTypes GTy
open import DenotationalSemantics.Model.Example.PSh.Monad.Core S Wld GTy
open import DenotationalSemantics.Model.Example.PSh.Monad.Effects S Wld GTy

open import DenotationalSemantics.Model.Category
open Category PShCat using (mapˣᵐ; map⇒ᵐ; exp-strᵐ; fstᵐ; sndᵐ; ⟨_,_⟩ᵐ)

open import DenotationalSemantics.Model.Modality.BoxCoalg
  PShCat (GradeSystem.RGrade Grades) PShFut

open import DenotationalSemantics.Model.Example.PSh.Monad.Handling.Core S Wld GTy

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

-- The fold commutes with a grade transport.

T-alg-ε-substˢ : ∀ {P A ε₁ ε₂ ε' w} → (bc : BoxCoalg P) → (h : Handlerˢ P A)
               → (pv : carrier P w) → (e : ε₁ ≡ ε₂)
               → (t : Tˢ (Tᵒ A ε') ε₁ w)
               → T-alg-of-handlerˢ bc h pv (ε-substˢ e t)
               ≡ ε-substˢ (cong (_·ₑ ε') e) (T-alg-of-handlerˢ bc h pv t)
T-alg-ε-substˢ bc h pv refl t = refl

-- THE HANDLER IS UNIFORM IN ITS GRADE INDEX
--
-- The algebra law applies the handler's clause at two grades that are only
-- *propositionally* equal — `(ε₁ ·ₑ ε') ·ₑ ε''` on the left, `ε₁ ·ₑ (ε' ·ₑ ε'')`
-- on the right. A `Handlerˢ` is an arbitrary family indexed by the grade, so
-- those are different morphisms at different types; but they coincide up to
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
             → app (h op ε₁) (pv , (v , b))
             ≈ᵗ ε-substˢ (cong (op-grade op ·ₑ_) (sym e))
                  (app (h op ε₂) (pv , (v , box-ε-substˢ e b)))
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
                   → (f : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ) ] w' → Tˢ A ε₁ w')
                   → (fn : ∀ {w' w''} (q : w ⊑[ mapᵉ (of-natᵉ τ) ] w')
                             (r : w' ⊑[ uᵣ ] w'')
                         → f (⊑ρ∘ᵘ q r) ≈ᵗ transportᵗ r (f q))
                   → ∀ {w' w''} (q : w ⊑[ mapᵉ (of-natᵉ τ) ] w') (r : w' ⊑[ uᵣ ] w'')
                   → ε-substˢ e (f (⊑ρ∘ᵘ q r)) ≈ᵗ transportᵗ r (ε-substˢ e (f q))
delay-ε-substˢ-nat e f fn q r =
  ≈ᵗ-trans (ε-substˢ-congᵗ e (fn q r))
           (≡→≈ᵗ (sym (transportᵗ-ε-substˢ r e (f q))))

delay-ε-substˢ : ∀ {A ε₁ ε₂ τ w} → (e : ε₁ ≡ ε₂)
               → (f : ∀ {w'} → w ⊑[ mapᵉ (of-natᵉ τ) ] w' → Tˢ A ε₁ w')
               → (fn : ∀ {w' w''} (q : w ⊑[ mapᵉ (of-natᵉ τ) ] w') (r : w' ⊑[ uᵣ ] w'')
                     → f (⊑ρ∘ᵘ q r) ≈ᵗ transportᵗ r (f q))
               → delay-node τ (λ q → ε-substˢ e (f q)) (delay-ε-substˢ-nat e f fn)
               ≈ᵗ ε-substˢ (cong (of-natᵉ τ ·ₑ_) e) (delay-node τ f fn)
delay-ε-substˢ refl f fn = delay-≈ (λ q → ≈ᵗ-refl _)

-- The fold is an algebra: folding a two-layer tree is folding the outer layer
-- after folding each inner one. By induction on the tree — at each node the
-- fold and the multiplication agree, so the two transports coincide.

{-# TERMINATING #-}
T-alg-of-handlerˢ-μˢ : ∀ {P A ε ε' ε'' w} → (bc : BoxCoalg P) → (h : Handlerˢ P A)
                     → (pv : carrier P w)
                     → (t : Tˢ (Tᵒ (Tᵒ A ε'') ε') ε w)
                     → T-alg-of-handlerˢ {ε = ε ·ₑ ε'} {ε''} bc h pv (μˢ t)
                     ≈ᵗ ε-substˢ (sym (·ₑ-assoc ε ε' ε''))
                          (T-alg-of-handlerˢ {ε = ε} {ε' ·ₑ ε''} bc h pv
                            (Tˢᶠ (T-alg-of-handlerᵀ bc h)
                              (strˢ _ (app (BoxCoalg.necᵉ bc) pv) t)))
T-alg-of-handlerˢ-μˢ {P = P} {ε' = ε'} {ε'' = ε''} bc h pv (leaf t) =
  ≈ᵗ-trans (≡→≈ᵗ (T-alg-ε-substˢ bc h pv (sym (·ₑ-identityˡ ε')) t))
  (≈ᵗ-trans (ε-substˢ-congᵗ (cong (_·ₑ ε'') (sym (·ₑ-identityˡ ε')))
               (T-alg-of-handlerˢ-congᵖ bc h
                 (≈-sym P (≈-trans P (BoxCoalg.necᵉ-≤ bc (≾ᵣ-reflexive (sym map-uᵉ)) pv ⊑-refl)
                                     (≈-trans P (BoxCoalg.necᵉ-u bc pv ⊑-refl)
                                                (transport-refl P pv))))
                 t))
            (≡→≈ᵗ (trans (cong (λ e → ε-substˢ e (T-alg-of-handlerˢ bc h _ t)) uip)
                         (sym (ε-substˢ-trans (sym (·ₑ-identityˡ (ε' ·ₑ ε'')))
                                              (sym (·ₑ-assoc uₑ ε' ε''))
                                              (T-alg-of-handlerˢ bc h _ t))))))
T-alg-of-handlerˢ-μˢ bc h pv (op-node op v k kc kn)   = {!!}
T-alg-of-handlerˢ-μˢ bc h pv (delay-node τ k kn)      = {!!}
T-alg-of-handlerˢ-μˢ {P = P} {ε = ε} {ε' = ε'} {ε'' = ε''} bc h pv (sub {ε = ε₀} p t) =
  ≈ᵗ-trans
    (sub-≈ (≈ᵗ-trans (T-alg-of-handlerˢ-μˢ bc h pv t)
                     (ε-substˢ-congᵗ (sym (·ₑ-assoc ε₀ ε' ε''))
                        (T-alg-of-handlerˢ-congᵗ bc h pv
                          (Tˢᶠ-congᵗ (T-alg-of-handlerᵀ bc h)
                            (strˢ-congᵗ P
                              (λ q → ≈-sym P (BoxCoalg.necᵉ-≤ bc (map-monotoneᵉ p) pv q))
                              (≈ᵗ-refl t)))))))
    (≈ᵗ-trans (sub-ε-substˢ (sym (·ₑ-assoc ε₀ ε' ε'')) (·ₑ-monoˡ-≾ₑ (·ₑ-monoˡ-≾ₑ p)) q' _)
              (≈ᵗ-sym (ε-substˢ-sub' (·ₑ-monoˡ-≾ₑ p) (sym (·ₑ-assoc ε ε' ε'')) q' _)))
  where
    q' : ε₀ ·ₑ (ε' ·ₑ ε'') ≾ₑ (ε ·ₑ ε') ·ₑ ε''
    q' = ≾ₑ-trans (≾ₑ-reflexive (sym (·ₑ-assoc ε₀ ε' ε'')))
                  (·ₑ-monoˡ-≾ₑ (·ₑ-monoˡ-≾ₑ p))

-- Packaging the two laws as morphism equations.

T-alg-of-handlerᵀ-μᵀ : ∀ {P A ε ε' ε''} → (bc : BoxCoalg P) → (h : Handlerˢ P A)
                     → T-alg-of-handlerᵀ {P} {A} {ε ·ₑ ε'} {ε''} bc h
                         ∘ᵖ mapˣᵐ idᵖ (μᵀ {Tᵒ A ε''} {ε} {ε'})
                     ≈ᵖ ε-substᵀ (sym (·ₑ-assoc ε ε' ε''))
                         ∘ᵖ T-alg-of-handlerᵀ {P} {A} {ε} {ε' ·ₑ ε''} bc h
                         ∘ᵖ ⟨ fstᵐ
                            , Tᶠ (T-alg-of-handlerᵀ {P} {A} {ε'} {ε''} bc h)
                              ∘ᵖ strᵀ
                              ∘ᵖ mapˣᵐ (BoxCoalg.necᵉ bc {mapᵉ ε}) idᵖ ⟩ᵐ
T-alg-of-handlerᵀ-μᵀ bc h (pv , t) = T-alg-of-handlerˢ-μˢ bc h pv t
