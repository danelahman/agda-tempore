------------------------------------------------------------------------
-- Effect handling for the free graded monad.                           --
--                                                                    --
-- A handler is a family of *clause morphisms*, one per operation `op`   --
-- and residual effect grade `ε''`. `T-alg-of-handlerˢ` folds the tree,  --
-- reinterpreting every `op-node` by the matching clause, keeping delays --
-- as delays, and returning the leaf value (regraded).                   --
--                                                                    --
-- At an operation the clause takes its continuation as a boxed          --
-- exponential; `handler-box` rebuilds it from the node's stored          --
-- continuation `k` and coherence witnesses `k-cong`/`k-nat`, advanced    --
-- across the fold's own congruence (`-cong`) and world-naturality        --
-- (`-nat`) — the three defined mutually, as for `μˢ`. The clauses being  --
-- morphisms (natural families) is what lets the fold recurse under an    --
-- operation, reusing the same clauses at the reached world.             --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.GroundTypes
import DenotationalSemantics.Model.Example.PSh.Base as B
import DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module DenotationalSemantics.Model.Example.PSh.Monad.Handling
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)

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
open Category PShCat using (mapˣᵐ; map⇒ᵐ)

-- A handler: a clause morphism for every operation and residual grade.

Handlerˢ : PSh → Set
Handlerˢ A = (op : Op) → (ε'' : E)
           → ⟦ param op ⟧ᵍ ×ᵖ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A ε'')
               →ᵖ Tᵒ A (op-grade op ·ₑ ε'')

-- The T-algebra folding a handler over a computation tree, together with
-- its congruence and world-naturality (defined mutually, as for `μˢ`).
--
-- At an `op-node` the fold reinterprets the operation by the matching
-- clause `h op`. The clause expects its continuation as a *boxed
-- exponential*, which `handler-box` rebuilds from the node's stored
-- continuation `k` and its coherence witnesses `k-cong`/`k-nat`: the
-- exponential's `fun-cong`/`fun-nat` come from `k-cong`/`k-nat` (advanced
-- across the fold's own congruence/naturality), and the box's `fun-nat`
-- from the proof-irrelevance of accessibility.
--
-- `TERMINATING`: the fold recurses through the function-valued
-- continuations, structurally smaller trees masked by the mutual
-- `-cong`/`-nat` (as for `μˢ`, `strˢ`).

mutual

  {-# TERMINATING #-}

  T-alg-of-handlerˢ : ∀ {A ε ε' w} → Handlerˢ A → Tˢ (Tᵒ A ε') ε w → Tˢ A (ε ·ₑ ε') w
  T-alg-of-handlerˢ {ε' = ε'} h (leaf s) =
    ε-substˢ (sym (·ₑ-identityˡ ε')) s
  T-alg-of-handlerˢ {ε' = ε'} h (op-node {ε = ε₀} op v k kc kn) =
    ε-substˢ (sym (·ₑ-assoc (op-grade op) ε₀ ε'))
      (app (h op (ε₀ ·ₑ ε')) (v , handler-box h op k kc kn))
  T-alg-of-handlerˢ {ε' = ε'} h (delay-node {ε = ε₀} τ k kn) =
    ε-substˢ (sym (·ₑ-assoc (of-natᵉ τ) ε₀ ε'))
      (delay-node τ (λ q → T-alg-of-handlerˢ h (k q))
        (λ q r → ≈ᵗ-trans (T-alg-of-handlerˢ-cong h (kn q r))
                          (T-alg-of-handlerˢ-nat h r (k q))))
  T-alg-of-handlerˢ h (sub p t) =
    sub (·ₑ-monoˡ-≾ₑ p) (T-alg-of-handlerˢ h t)

  -- The clause's boxed continuation, folded and rebundled.

  handler-box : ∀ {A ε₀ ε' w} (h : Handlerˢ A) (op : Op)
      → (k : ∀ {w'} → w ⊑[ mapᵉ (op-grade op) ] w' → carrier ⟦ arity op ⟧ᵍ w'
           → Tˢ (Tᵒ A ε') ε₀ w')
      → (kc : ∀ {w'} (q : w ⊑[ mapᵉ (op-grade op) ] w')
                {y y' : carrier ⟦ arity op ⟧ᵍ w'}
            → _≈_ ⟦ arity op ⟧ᵍ y y' → k q y ≈ᵗ k q y')
      → (kn : ∀ {w' w''} (q : w ⊑[ mapᵉ (op-grade op) ] w') (r : w' ⊑[ uᵣ ] w'')
                (y : carrier ⟦ arity op ⟧ᵍ w')
            → k (⊑ρ∘ᵘ q r) (transport ⟦ arity op ⟧ᵍ r y) ≈ᵗ transportᵗ r (k q y))
      → [ mapᵉ (op-grade op) ]ᶜ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A (ε₀ ·ₑ ε')) w
  handler-box h op k kc kn = mk[]
    (λ q → mk⇒
      (λ r y → T-alg-of-handlerˢ h (k (⊑ρ∘ᵘ q r) y))
      (λ r e → T-alg-of-handlerˢ-cong h (kc (⊑ρ∘ᵘ q r) e))
      (λ r s y → ≈ᵗ-trans
        (T-alg-of-handlerˢ-cong h
          (≡→≈ᵗ (cong (λ z → k z (transport ⟦ arity op ⟧ᵍ s y)) (⊑-irrelevant _ _))))
        (≈ᵗ-trans
          (T-alg-of-handlerˢ-cong h (kn (⊑ρ∘ᵘ q r) s y))
          (T-alg-of-handlerˢ-nat h s (k (⊑ρ∘ᵘ q r) y)))))
    (λ q r p y → T-alg-of-handlerˢ-cong h (≡→≈ᵗ (cong (λ z → k z y) (⊑-irrelevant _ _))))

  T-alg-of-handlerˢ-cong : ∀ {A ε ε' w} (h : Handlerˢ A) {t t' : Tˢ (Tᵒ A ε') ε w}
                         → t ≈ᵗ t' → T-alg-of-handlerˢ h t ≈ᵗ T-alg-of-handlerˢ h t'
  T-alg-of-handlerˢ-cong h (leaf-≈ e)             = ε-substˢ-congᵗ _ e
  T-alg-of-handlerˢ-cong h (op-≈ {op = op} ev ek) =
    ε-substˢ-congᵗ _ (app-cong (h op _)
      (ev , (λ q p y → T-alg-of-handlerˢ-cong h (ek (⊑ρ∘ᵘ q p) y))))
  T-alg-of-handlerˢ-cong h (delay-≈ ek)           =
    ε-substˢ-congᵗ _ (delay-≈ (λ q → T-alg-of-handlerˢ-cong h (ek q)))
  T-alg-of-handlerˢ-cong h (sub-≈ et)             =
    sub-≈ (T-alg-of-handlerˢ-cong h et)
  T-alg-of-handlerˢ-cong h sub-u                 = sub-u
  T-alg-of-handlerˢ-cong h sub-∘                 = sub-∘
  T-alg-of-handlerˢ-cong h (≈ᵗ-sym et)           =
    ≈ᵗ-sym (T-alg-of-handlerˢ-cong h et)
  T-alg-of-handlerˢ-cong h (≈ᵗ-trans et et')     =
    ≈ᵗ-trans (T-alg-of-handlerˢ-cong h et) (T-alg-of-handlerˢ-cong h et')

  T-alg-of-handlerˢ-nat : ∀ {A ε ε' w w'} (h : Handlerˢ A) (p : w ⊑[ uᵣ ] w')
                          (t : Tˢ (Tᵒ A ε') ε w)
                        → T-alg-of-handlerˢ h (transportᵗ p t)
                        ≈ᵗ transportᵗ p (T-alg-of-handlerˢ h t)
  T-alg-of-handlerˢ-nat h p (leaf s) =
    ≡→≈ᵗ (sym (transportᵗ-ε-substˢ p (sym (·ₑ-identityˡ _)) s))
  T-alg-of-handlerˢ-nat h p (op-node {ε = ε₀} op v k kc kn) =
    ≈ᵗ-trans
      (ε-substˢ-congᵗ (sym (·ₑ-assoc (op-grade op) ε₀ _))
        (app-cong (h op _)
          (≈-refl ⟦ param op ⟧ᵍ ,
           (λ q r y → T-alg-of-handlerˢ-cong h
             (≡→≈ᵗ (cong (λ z → k z y) (⊑-irrelevant _ _)))))))
      (≈ᵗ-trans
        (ε-substˢ-congᵗ (sym (·ₑ-assoc (op-grade op) ε₀ _))
          (nat (h op _) p (v , handler-box h op k kc kn)))
        (≡→≈ᵗ (sym (transportᵗ-ε-substˢ p (sym (·ₑ-assoc (op-grade op) ε₀ _)) _))))
  T-alg-of-handlerˢ-nat h p (delay-node {ε = ε₀} τ k kn) =
    ≈ᵗ-trans
      (ε-substˢ-congᵗ (sym (·ₑ-assoc (of-natᵉ τ) ε₀ _)) (delay-≈ (λ q → ≈ᵗ-refl _)))
      (≡→≈ᵗ (sym (transportᵗ-ε-substˢ p (sym (·ₑ-assoc (of-natᵉ τ) ε₀ _)) _)))
  T-alg-of-handlerˢ-nat h p (sub e t) =
    sub-≈ (T-alg-of-handlerˢ-nat h p t)

T-alg-of-handlerᵀ : ∀ {A ε ε'} → Handlerˢ A → Tᵒ (Tᵒ A ε') ε →ᵖ Tᵒ A (ε ·ₑ ε')
T-alg-of-handlerᵀ h =
  pmap (T-alg-of-handlerˢ h) (T-alg-of-handlerˢ-cong h) (λ p t → T-alg-of-handlerˢ-nat h p t)

-- The three algebra laws (up to `_≈ᵗ_`): each side folds to the same tree
-- (returning / re-delaying / applying the clause to the rebuilt box).

T-alg-of-handlerᵀ-ηᵀ : ∀ {A ε'} → (h : Handlerˢ A)
                     → T-alg-of-handlerᵀ h ∘ᵖ ηᵀ {Tᵒ A ε'}
                     ≈ᵖ ε-substᵀ (sym (·ₑ-identityˡ ε'))
T-alg-of-handlerᵀ-ηᵀ h s = ≈ᵗ-refl _

T-alg-of-handlerᵀ-delayᵀ : ∀ {A ε' ε''} → (τ : ℕ) → (h : Handlerˢ A)
                         → T-alg-of-handlerᵀ h ∘ᵖ delayᵀ {Tᵒ A ε''} {ε'} τ
                         ≈ᵖ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε''))
                           ∘ᵖ delayᵀ τ ∘ᵖ [ of-natʳ τ ]ᶠ (T-alg-of-handlerᵀ h)
T-alg-of-handlerᵀ-delayᵀ τ h x =
  ε-substˢ-congᵗ (sym (·ₑ-assoc (of-natᵉ τ) _ _)) (delay-≈ (λ q → ≈ᵗ-refl _))

T-alg-of-handlerᵀ-opᵀ : ∀ {A ε' ε''} → (op : Op) → (h : Handlerˢ A)
                      → T-alg-of-handlerᵀ h ∘ᵖ opᵀ {Tᵒ A ε''} {ε'} op
                      ≈ᵖ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε' ε''))
                        ∘ᵖ h op (ε' ·ₑ ε'')
                        ∘ᵖ mapˣᵐ idᵖ
                             ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵖ (T-alg-of-handlerᵀ h)))
T-alg-of-handlerᵀ-opᵀ op h (v , boxk) =
  ε-substˢ-congᵗ (sym (·ₑ-assoc (op-grade op) _ _))
    (app-cong (h op _)
      (≈-refl ⟦ param op ⟧ᵍ ,
       (λ q p y → T-alg-of-handlerˢ-cong h (fun-nat boxk q p ⊑-refl y))))
