------------------------------------------------------------------------
-- Effect handling: the algebra (μ) law and its grade-transport lemmas. --
------------------------------------------------------------------------

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

T-alg-ε-substˢ : ∀ {A ε₁ ε₂ ε' w} → (h : Handlerˢ A) → (e : ε₁ ≡ ε₂)
               → (t : Tˢ (Tᵒ A ε') ε₁ w)
               → T-alg-of-handlerˢ h (ε-substˢ e t)
               ≡ ε-substˢ (cong (_·ₑ ε') e) (T-alg-of-handlerˢ h t)
T-alg-ε-substˢ h refl t = refl

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

app-ε-substˢ : ∀ {A ε₁ ε₂ w} → (h : Handlerˢ A) → (op : Op) → (e : ε₁ ≡ ε₂)
             → (v : carrier ⟦ param op ⟧ᵍ w)
             → (b : [ mapᵉ (op-grade op) ]ᶜ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A ε₁) w)
             → app (h op ε₁) (v , b)
             ≈ᵗ ε-substˢ (cong (op-grade op ·ₑ_) (sym e))
                  (app (h op ε₂) (v , box-ε-substˢ e b))
app-ε-substˢ h op refl v b = ≈ᵗ-refl _

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
T-alg-of-handlerˢ-μˢ : ∀ {A ε ε' ε'' w} → (h : Handlerˢ A)
                     → (t : Tˢ (Tᵒ (Tᵒ A ε'') ε') ε w)
                     → T-alg-of-handlerˢ {ε = ε ·ₑ ε'} {ε''} h (μˢ t)
                     ≈ᵗ ε-substˢ (sym (·ₑ-assoc ε ε' ε''))
                          (T-alg-of-handlerˢ {ε = ε} {ε' ·ₑ ε''} h
                            (Tˢᶠ (T-alg-of-handlerᵀ {ε = ε'} {ε''} h) t))
-- leaf: the left transports the folded inner tree once (`T-alg-ε-substˢ`), the
-- right twice; both composites are proofs of `ε' ·ₑ ε'' ≡ (uₑ ·ₑ ε') ·ₑ ε''`,
-- so `uip` identifies them.
T-alg-of-handlerˢ-μˢ {ε' = ε'} {ε'' = ε''} h (leaf t) =
  ≡→≈ᵗ (trans (T-alg-ε-substˢ h (sym (·ₑ-identityˡ ε')) t)
        (trans (cong (λ e → ε-substˢ e (T-alg-of-handlerˢ h t)) uip)
               (sym (ε-substˢ-trans (sym (·ₑ-identityˡ (ε' ·ₑ ε'')))
                                    (sym (·ₑ-assoc uₑ ε' ε''))
                                    (T-alg-of-handlerˢ h t)))))
-- op: both sides apply the handler's clause, but at grades that differ by an
-- associativity — `app-ε-substˢ` bridges them. The two boxed continuations then
-- agree pointwise, which is exactly the inductive hypothesis, and the residual
-- transports coincide by `uip`.
T-alg-of-handlerˢ-μˢ {ε' = ε'} {ε'' = ε''} h (op-node {ε = ε₁} op v k kc kn) =
  ≈ᵗ-trans (≡→≈ᵗ (T-alg-ε-substˢ h (sym (·ₑ-assoc (op-grade op) ε₁ ε')) _))
  (≈ᵗ-trans (ε-substˢ-congᵗ E1 (ε-substˢ-congᵗ E2
              (app-ε-substˢ h op (·ₑ-assoc ε₁ ε' ε'') v _)))
  (≈ᵗ-trans (ε-substˢ-congᵗ E1 (ε-substˢ-congᵗ E2 (ε-substˢ-congᵗ E3
              (app-cong (h op (ε₁ ·ₑ (ε' ·ₑ ε'')))
                        (≈-refl ⟦ param op ⟧ᵍ , box-eq)))))
            (≡→≈ᵗ (trans (cong (ε-substˢ E1) (ε-substˢ-trans E3 E2 X))
                  (trans (ε-substˢ-trans (trans E3 E2) E1 X)
                  (trans (cong (λ z → ε-substˢ z X) uip)
                         (sym (ε-substˢ-trans e2 e1 X))))))))
  where
    -- the target of the handler's clause, at the re-associated grade
    X = B.app (h op (ε₁ ·ₑ (ε' ·ₑ ε'')))
              (v , handler-box h op
                     (λ q' y → Tˢᶠ (T-alg-of-handlerᵀ h) (k q' y))
                     (λ q' e → Tˢᶠ-congᵗ (T-alg-of-handlerᵀ h) (kc q' e))
                     (λ q' r y → ≈ᵗ-trans (Tˢᶠ-congᵗ (T-alg-of-handlerᵀ h) (kn q' r y))
                                          (Tˢᶠ-natᵗ (T-alg-of-handlerᵀ h) r (k q' y))))

    -- the transports the two sides accumulate (equal, by `uip`)
    E1 = cong (_·ₑ ε'') (sym (·ₑ-assoc (op-grade op) ε₁ ε'))
    E2 = sym (·ₑ-assoc (op-grade op) (ε₁ ·ₑ ε') ε'')
    E3 = cong (op-grade op ·ₑ_) (sym (·ₑ-assoc ε₁ ε' ε''))
    e1 = sym (·ₑ-assoc (op-grade op ·ₑ ε₁) ε' ε'')
    e2 = sym (·ₑ-assoc (op-grade op) ε₁ (ε' ·ₑ ε''))

    -- the two boxed continuations agree: pointwise this is the IH, modulo the
    -- transport that `box-ε-substˢ` carries
    box-eq : ∀ {w'} (q : _ ⊑[ mapᵉ (op-grade op) ] w')
           → _≈_ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ _ (ε₁ ·ₑ (ε' ·ₑ ε'')))
                 (F.fun (box-ε-substˢ (·ₑ-assoc ε₁ ε' ε'')
                          (handler-box h op (λ q' y → μˢ (k q' y))
                            (λ q' e → μˢ-congᵗ (kc q' e))
                            (λ q' r y → ≈ᵗ-trans (μˢ-congᵗ (kn q' r y))
                                                 (μˢ-natᵗ r (k q' y))))) q)
                 (F.fun (handler-box h op
                          (λ q' y → Tˢᶠ (T-alg-of-handlerᵀ h) (k q' y))
                          (λ q' e → Tˢᶠ-congᵗ (T-alg-of-handlerᵀ h) (kc q' e))
                          (λ q' r y → ≈ᵗ-trans
                            (Tˢᶠ-congᵗ (T-alg-of-handlerᵀ h) (kn q' r y))
                            (Tˢᶠ-natᵗ (T-alg-of-handlerᵀ h) r (k q' y)))) q)
    box-eq q r y =
      ≈ᵗ-trans (≡→≈ᵗ (box-ε-substˢ-fun (·ₑ-assoc ε₁ ε' ε'') _ q r y))
      (≈ᵗ-trans (ε-substˢ-congᵗ (·ₑ-assoc ε₁ ε' ε'')
                  (T-alg-of-handlerˢ-μˢ h (k (⊑ρ∘ᵘ q r) y)))
                (≡→≈ᵗ (trans (ε-substˢ-trans (sym (·ₑ-assoc ε₁ ε' ε''))
                                             (·ₑ-assoc ε₁ ε' ε'')
                                             (T-alg-of-handlerˢ h
                                               (Tˢᶠ (T-alg-of-handlerᵀ h)
                                                    (k (⊑ρ∘ᵘ q r) y))))
                             (cong (λ z → ε-substˢ z (T-alg-of-handlerˢ h
                                            (Tˢᶠ (T-alg-of-handlerᵀ h)
                                                 (k (⊑ρ∘ᵘ q r) y)))) uip))))

-- delay: the same shape as `op`, without the handler clause — the delay node
-- is rebuilt on both sides, so the continuations need only agree pointwise
-- (the IH), and the transports again coincide by `uip`.
T-alg-of-handlerˢ-μˢ {ε' = ε'} {ε'' = ε''} h (delay-node {ε = ε₁} τ k kn) =
  ≈ᵗ-trans (≡→≈ᵗ (T-alg-ε-substˢ h (sym (·ₑ-assoc (of-natᵉ τ) ε₁ ε')) _))
  (≈ᵗ-trans (ε-substˢ-congᵗ E1 (ε-substˢ-congᵗ E2
              (≈ᵗ-trans (delay-≈ (λ q → T-alg-of-handlerˢ-μˢ h (k q)))
                        (delay-ε-substˢ (sym (·ₑ-assoc ε₁ ε' ε''))
                          (λ q → T-alg-of-handlerˢ h
                                   (Tˢᶠ (T-alg-of-handlerᵀ h) (k q)))
                          -- the folded continuation's own coherence witness
                          (λ q r → ≈ᵗ-trans
                            (T-alg-of-handlerˢ-cong h
                              (≈ᵗ-trans (Tˢᶠ-congᵗ (T-alg-of-handlerᵀ h) (kn q r))
                                        (Tˢᶠ-natᵗ (T-alg-of-handlerᵀ h) r (k q))))
                            (T-alg-of-handlerˢ-nat h r
                              (Tˢᶠ (T-alg-of-handlerᵀ h) (k q))))))))
            (≡→≈ᵗ (trans (cong (ε-substˢ E1) (ε-substˢ-trans E3 E2 X))
                  (trans (ε-substˢ-trans (trans E3 E2) E1 X)
                  (trans (cong (λ z → ε-substˢ z X) uip)
                         (sym (ε-substˢ-trans e2 e1 X)))))))
  where
    X = delay-node τ (λ q → T-alg-of-handlerˢ h
                              (Tˢᶠ (T-alg-of-handlerᵀ h) (k q)))
                     (λ q r → ≈ᵗ-trans
                       (T-alg-of-handlerˢ-cong h
                         (≈ᵗ-trans (Tˢᶠ-congᵗ (T-alg-of-handlerᵀ h) (kn q r))
                                   (Tˢᶠ-natᵗ (T-alg-of-handlerᵀ h) r (k q))))
                       (T-alg-of-handlerˢ-nat h r
                         (Tˢᶠ (T-alg-of-handlerᵀ h) (k q))))

    E1 = cong (_·ₑ ε'') (sym (·ₑ-assoc (of-natᵉ τ) ε₁ ε'))
    E2 = sym (·ₑ-assoc (of-natᵉ τ) (ε₁ ·ₑ ε') ε'')
    E3 = cong (of-natᵉ τ ·ₑ_) (sym (·ₑ-assoc ε₁ ε' ε''))
    e1 = sym (·ₑ-assoc (of-natᵉ τ ·ₑ ε₁) ε' ε'')
    e2 = sym (·ₑ-assoc (of-natᵉ τ) ε₁ (ε' ·ₑ ε''))
-- sub: both sides push the coercion node outwards; the transports it carries
-- past are absorbed on each side (`sub`'s witnesses are irrelevant to `_≈ᵗ_`).
T-alg-of-handlerˢ-μˢ {ε = ε} {ε' = ε'} {ε'' = ε''} h (sub {ε = ε₀} p t) =
  ≈ᵗ-trans (sub-≈ (T-alg-of-handlerˢ-μˢ h t))
  (≈ᵗ-trans (sub-ε-substˢ (sym (·ₑ-assoc ε₀ ε' ε''))
                          (·ₑ-monoˡ-≾ₑ (·ₑ-monoˡ-≾ₑ p)) q' _)
            (≈ᵗ-sym (ε-substˢ-sub' (·ₑ-monoˡ-≾ₑ p)
                                   (sym (·ₑ-assoc ε ε' ε'')) q' _)))
  where
    -- the coercion witness, taken across the re-association
    q' : ε₀ ·ₑ (ε' ·ₑ ε'') ≾ₑ (ε ·ₑ ε') ·ₑ ε''
    q' = ≾ₑ-trans (≾ₑ-reflexive (sym (·ₑ-assoc ε₀ ε' ε'')))
                  (·ₑ-monoˡ-≾ₑ (·ₑ-monoˡ-≾ₑ p))

-- Packaging the two laws as morphism equations.

T-alg-of-handlerᵀ-μᵀ : ∀ {A ε ε' ε''} → (h : Handlerˢ A)
                     → T-alg-of-handlerᵀ {A} {ε ·ₑ ε'} {ε''} h ∘ᵖ μᵀ {Tᵒ A ε''} {ε} {ε'}
                     ≈ᵖ ε-substᵀ (sym (·ₑ-assoc ε ε' ε''))
                         ∘ᵖ T-alg-of-handlerᵀ {A} {ε} {ε' ·ₑ ε''} h
                         ∘ᵖ Tᶠ (T-alg-of-handlerᵀ {A} {ε'} {ε''} h)
T-alg-of-handlerᵀ-μᵀ h t = T-alg-of-handlerˢ-μˢ h t
