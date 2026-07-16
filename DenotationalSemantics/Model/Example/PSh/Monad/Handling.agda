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

-- A handler parameterised by an eternal object `P`: a clause morphism for
-- every operation and residual grade, closing over `P`.

Handlerˢ : PSh → PSh → Set
Handlerˢ P A = (op : Op) → (ε'' : E)
           → P ×ᵖ (⟦ param op ⟧ᵍ ×ᵖ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A ε''))
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

  T-alg-of-handlerˢ : ∀ {P A ε ε' w} → BoxCoalg P → Handlerˢ P A
                    → carrier P w → Tˢ (Tᵒ A ε') ε w → Tˢ A (ε ·ₑ ε') w
  T-alg-of-handlerˢ {ε' = ε'} bc h pv (leaf s) =
    ε-substˢ (sym (·ₑ-identityˡ ε')) s
  T-alg-of-handlerˢ {ε' = ε'} bc h pv (op-node {ε = ε₀} op v k kc kn) =
    ε-substˢ (sym (·ₑ-assoc (op-grade op) ε₀ ε'))
      (app (h op (ε₀ ·ₑ ε')) (pv , (v , handler-box bc pv h op k kc kn)))
  T-alg-of-handlerˢ {ε' = ε'} bc h pv (delay-node {ε = ε₀} τ k kn) =
    ε-substˢ (sym (·ₑ-assoc (of-natᵉ τ) ε₀ ε'))
      (delay-node τ (λ q → T-alg-of-handlerˢ bc h (fun (app (BoxCoalg.necᵉ bc) pv) q) (k q))
        (λ q r → ≈ᵗ-trans
          (T-alg-of-handlerˢ-congᵖ bc h (fun-nat (app (BoxCoalg.necᵉ bc) pv) q r) (k (⊑ρ∘ᵘ q r)))
          (≈ᵗ-trans
            (T-alg-of-handlerˢ-congᵗ bc h _ (kn q r))
            (T-alg-of-handlerˢ-nat bc h r (fun (app (BoxCoalg.necᵉ bc) pv) q) (k q)))))
  T-alg-of-handlerˢ bc h pv (sub p t) =
    sub (·ₑ-monoˡ-≾ₑ p) (T-alg-of-handlerˢ bc h pv t)

  -- The clause's boxed continuation, folded and rebundled. The eternal
  -- parameter `pv` is carried into the folded sub-computations at each future
  -- world via `necᵉ` (which crosses the operation's box `[ mapᵉ (op-grade op) ]`).

  handler-box : ∀ {P A ε₀ ε' w} (bc : BoxCoalg P) (pv : carrier P w) (h : Handlerˢ P A) (op : Op)
      → (k : ∀ {w'} → w ⊑[ mapᵉ (op-grade op) ] w' → carrier ⟦ arity op ⟧ᵍ w'
           → Tˢ (Tᵒ A ε') ε₀ w')
      → (kc : ∀ {w'} (q : w ⊑[ mapᵉ (op-grade op) ] w')
                {y y' : carrier ⟦ arity op ⟧ᵍ w'}
            → _≈_ ⟦ arity op ⟧ᵍ y y' → k q y ≈ᵗ k q y')
      → (kn : ∀ {w' w''} (q : w ⊑[ mapᵉ (op-grade op) ] w') (r : w' ⊑[ uᵣ ] w'')
                (y : carrier ⟦ arity op ⟧ᵍ w')
            → k (⊑ρ∘ᵘ q r) (transport ⟦ arity op ⟧ᵍ r y) ≈ᵗ transportᵗ r (k q y))
      → [ mapᵉ (op-grade op) ]ᶜ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A (ε₀ ·ₑ ε')) w
  handler-box bc pv h op k kc kn = mk[]
    (λ q → mk⇒
      (λ r y → T-alg-of-handlerˢ bc h (fun (app (BoxCoalg.necᵉ bc) pv) (⊑ρ∘ᵘ q r)) (k (⊑ρ∘ᵘ q r) y))
      (λ r e → T-alg-of-handlerˢ-congᵗ bc h _ (kc (⊑ρ∘ᵘ q r) e))
      (λ r s y → ≈ᵗ-trans
        (T-alg-of-handlerˢ-congᵖ bc h
          (≈-trans _ ([]-fun-irr (app (BoxCoalg.necᵉ bc) pv) _ _)
                     (fun-nat (app (BoxCoalg.necᵉ bc) pv) (⊑ρ∘ᵘ q r) s))
          (k (⊑ρ∘ᵘ q (⊑ᵘ-trans r s)) (transport ⟦ arity op ⟧ᵍ s y)))
        (≈ᵗ-trans
          (T-alg-of-handlerˢ-congᵗ bc h _
            (≈ᵗ-trans
              (≡→≈ᵗ (cong (λ z → k z (transport ⟦ arity op ⟧ᵍ s y)) (⊑-irrelevant _ _)))
              (kn (⊑ρ∘ᵘ q r) s y)))
          (T-alg-of-handlerˢ-nat bc h s
            (fun (app (BoxCoalg.necᵉ bc) pv) (⊑ρ∘ᵘ q r)) (k (⊑ρ∘ᵘ q r) y)))))
    (λ q r p y → ≈ᵗ-trans
                   (T-alg-of-handlerˢ-congᵖ bc h
                     ([]-fun-irr (app (BoxCoalg.necᵉ bc) pv) _ _)
                     (k (⊑ρ∘ᵘ (⊑ρ∘ᵘ q r) p) y))
                   (T-alg-of-handlerˢ-congᵗ bc h _
                     (≡→≈ᵗ (cong (λ z → k z y) (⊑-irrelevant _ _)))))

  -- Congruence in the *tree* argument (the eternal parameter `pv` held fixed).

  T-alg-of-handlerˢ-congᵗ : ∀ {P A ε ε' w} (bc : BoxCoalg P) (h : Handlerˢ P A)
                            (pv : carrier P w) {t t' : Tˢ (Tᵒ A ε') ε w}
                          → t ≈ᵗ t' → T-alg-of-handlerˢ bc h pv t ≈ᵗ T-alg-of-handlerˢ bc h pv t'
  T-alg-of-handlerˢ-congᵗ bc h pv (leaf-≈ e)             = ε-substˢ-congᵗ _ e
  T-alg-of-handlerˢ-congᵗ bc h pv (op-≈ {op = op} ev ek) =
    ε-substˢ-congᵗ _ (app-cong (h op _)
      (≈-refl _ , (ev , (λ q p y → T-alg-of-handlerˢ-congᵗ bc h _ (ek (⊑ρ∘ᵘ q p) y)))))
  T-alg-of-handlerˢ-congᵗ bc h pv (delay-≈ ek)           =
    ε-substˢ-congᵗ _ (delay-≈ (λ q → T-alg-of-handlerˢ-congᵗ bc h _ (ek q)))
  T-alg-of-handlerˢ-congᵗ bc h pv (sub-≈ et)             =
    sub-≈ (T-alg-of-handlerˢ-congᵗ bc h pv et)
  T-alg-of-handlerˢ-congᵗ bc h pv sub-u                 = sub-u
  T-alg-of-handlerˢ-congᵗ bc h pv sub-∘                 = sub-∘
  T-alg-of-handlerˢ-congᵗ {ε' = ε'} bc h pv
    (sub-delay {ε = ε₁} {ε' = ε₁'} {τ = τ} {e = e}) =
    ≈ᵗ-trans
      (sub-ε-substᵗ (sym (·ₑ-assoc (of-natᵉ τ) ε₁ ε'))
                    (sym (·ₑ-assoc (of-natᵉ τ) ε₁' ε'))
                    (·ₑ-monoʳ-≾ₑ (·ₑ-monoˡ-≾ₑ e))
                    (·ₑ-monoˡ-≾ₑ (·ₑ-monoʳ-≾ₑ e))
                    _)
      (ε-substˢ-congᵗ _ sub-delay)
  T-alg-of-handlerˢ-congᵗ bc h pv (≈ᵗ-sym et)           =
    ≈ᵗ-sym (T-alg-of-handlerˢ-congᵗ bc h pv et)
  T-alg-of-handlerˢ-congᵗ bc h pv (≈ᵗ-trans et et')     =
    ≈ᵗ-trans (T-alg-of-handlerˢ-congᵗ bc h pv et) (T-alg-of-handlerˢ-congᵗ bc h pv et')

  -- Congruence in the eternal *parameter* argument (the tree held fixed).

  T-alg-of-handlerˢ-congᵖ : ∀ {P A ε ε' w} (bc : BoxCoalg P) (h : Handlerˢ P A)
                            {pv pv' : carrier P w} → _≈_ P pv pv'
                          → (t : Tˢ (Tᵒ A ε') ε w)
                          → T-alg-of-handlerˢ bc h pv t ≈ᵗ T-alg-of-handlerˢ bc h pv' t
  T-alg-of-handlerˢ-congᵖ bc h ep (leaf s)               = ≈ᵗ-refl _
  T-alg-of-handlerˢ-congᵖ bc h ep (op-node op v k kc kn) =
    ε-substˢ-congᵗ _ (app-cong (h op _)
      (ep , (≈-refl ⟦ param op ⟧ᵍ ,
        (λ q r y → T-alg-of-handlerˢ-congᵖ bc h
                     (app-cong (BoxCoalg.necᵉ bc) ep (⊑ρ∘ᵘ q r)) (k (⊑ρ∘ᵘ q r) y)))))
  T-alg-of-handlerˢ-congᵖ bc h ep (delay-node τ k kn)    =
    ε-substˢ-congᵗ _ (delay-≈
      (λ q → T-alg-of-handlerˢ-congᵖ bc h (app-cong (BoxCoalg.necᵉ bc) ep q) (k q)))
  T-alg-of-handlerˢ-congᵖ bc h ep (sub p t)              =
    sub-≈ (T-alg-of-handlerˢ-congᵖ bc h ep t)

  -- Naturality: the fold commutes with a (unit-graded) transport, jointly in
  -- the eternal parameter and the tree.

  T-alg-of-handlerˢ-nat : ∀ {P A ε ε' w w'} (bc : BoxCoalg P) (h : Handlerˢ P A)
                          (r : w ⊑[ uᵣ ] w') (pv : carrier P w)
                          (t : Tˢ (Tᵒ A ε') ε w)
                        → T-alg-of-handlerˢ bc h (transport P r pv) (transportᵗ r t)
                        ≈ᵗ transportᵗ r (T-alg-of-handlerˢ bc h pv t)
  T-alg-of-handlerˢ-nat bc h r pv (leaf s) =
    ≡→≈ᵗ (sym (transportᵗ-ε-substˢ r (sym (·ₑ-identityˡ _)) s))
  T-alg-of-handlerˢ-nat bc h r pv (op-node {ε = ε₀} op v k kc kn) =
    ≈ᵗ-trans
      (ε-substˢ-congᵗ (sym (·ₑ-assoc (op-grade op) ε₀ _))
        (app-cong (h op _)
          (≈-refl _ ,
           (≈-refl ⟦ param op ⟧ᵍ ,
            (λ q s y → ≈ᵗ-trans
              (T-alg-of-handlerˢ-congᵖ bc h
                (≈-trans _ (nat (BoxCoalg.necᵉ bc) r pv (⊑ρ∘ᵘ q s))
                           ([]-fun-irr (app (BoxCoalg.necᵉ bc) pv) _ _))
                (k _ y))
              (T-alg-of-handlerˢ-congᵗ bc h _
                (≡→≈ᵗ (cong (λ z → k z y) (⊑-irrelevant _ _)))))))))
      (≈ᵗ-trans
        (ε-substˢ-congᵗ (sym (·ₑ-assoc (op-grade op) ε₀ _))
          (nat (h op _) r (pv , (v , handler-box bc pv h op k kc kn))))
        (≡→≈ᵗ (sym (transportᵗ-ε-substˢ r (sym (·ₑ-assoc (op-grade op) ε₀ _)) _))))
  T-alg-of-handlerˢ-nat bc h r pv (delay-node {ε = ε₀} τ k kn) =
    ≈ᵗ-trans
      (ε-substˢ-congᵗ (sym (·ₑ-assoc (of-natᵉ τ) ε₀ _))
        (delay-≈ (λ q → T-alg-of-handlerˢ-congᵖ bc h
                          (nat (BoxCoalg.necᵉ bc) r pv q) (k (⊑ᵘ∘ρ r q)))))
      (≡→≈ᵗ (sym (transportᵗ-ε-substˢ r (sym (·ₑ-assoc (of-natᵉ τ) ε₀ _)) _)))
  T-alg-of-handlerˢ-nat bc h r pv (sub e t) =
    sub-≈ (T-alg-of-handlerˢ-nat bc h r pv t)

-- Joint congruence, assembled from the two one-sided congruences.

T-alg-of-handlerˢ-cong : ∀ {P A ε ε' w} (bc : BoxCoalg P) (h : Handlerˢ P A)
                         {pv pv' : carrier P w} {t t' : Tˢ (Tᵒ A ε') ε w}
                       → _≈_ P pv pv' → t ≈ᵗ t'
                       → T-alg-of-handlerˢ bc h pv t ≈ᵗ T-alg-of-handlerˢ bc h pv' t'
T-alg-of-handlerˢ-cong bc h {pv} {t' = t'} ep et =
  ≈ᵗ-trans (T-alg-of-handlerˢ-congᵗ bc h pv et) (T-alg-of-handlerˢ-congᵖ bc h ep t')

T-alg-of-handlerᵀ : ∀ {P A ε ε'} → BoxCoalg P → Handlerˢ P A
                  → P ×ᵖ Tᵒ (Tᵒ A ε') ε →ᵖ Tᵒ A (ε ·ₑ ε')
T-alg-of-handlerᵀ bc h =
  pmap
    (λ pt → T-alg-of-handlerˢ bc h (proj₁ pt) (proj₂ pt))
    (λ e → T-alg-of-handlerˢ-cong bc h (proj₁ e) (proj₂ e))
    (λ r pt → T-alg-of-handlerˢ-nat bc h r (proj₁ pt) (proj₂ pt))

-- The three algebra laws (up to `_≈ᵗ_`): each side folds to the same tree
-- (returning / re-delaying / applying the clause to the rebuilt box).

T-alg-of-handlerᵀ-ηᵀ : ∀ {P A ε'} → (bc : BoxCoalg P) → (h : Handlerˢ P A)
                     → T-alg-of-handlerᵀ bc h ∘ᵖ mapˣᵐ idᵖ (ηᵀ {Tᵒ A ε'})
                     ≈ᵖ ε-substᵀ (sym (·ₑ-identityˡ ε')) ∘ᵖ sndᵐ
T-alg-of-handlerᵀ-ηᵀ bc h x = ≈ᵗ-refl _

T-alg-of-handlerᵀ-delayᵀ : ∀ {P A ε' ε''} → (τ : ℕ) → (bc : BoxCoalg P) → (h : Handlerˢ P A)
                         → T-alg-of-handlerᵀ bc h ∘ᵖ mapˣᵐ idᵖ (delayᵀ {Tᵒ A ε''} {ε'} τ)
                         ≈ᵖ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε''))
                           ∘ᵖ delayᵀ τ
                           ∘ᵖ [ of-natʳ τ ]ᶠ (T-alg-of-handlerᵀ bc h)
                           ∘ᵖ []-monoidal
                           ∘ᵖ mapˣᵐ (BoxCoalg.necᵉ bc {of-natʳ τ}) idᵖ
T-alg-of-handlerᵀ-delayᵀ τ bc h (pv , boxT) =
  ε-substˢ-congᵗ (sym (·ₑ-assoc (of-natᵉ τ) _ _))
    (delay-≈ (λ q → T-alg-of-handlerˢ-congᵖ bc h
                      (≈-sym _ (BoxCoalg.necᵉ-≤ bc (≾ᵣ-reflexive map-of-natᵉ) pv q)) _))

T-alg-of-handlerᵀ-opᵀ : ∀ {P A ε' ε''} → (op : Op) → (bc : BoxCoalg P) → (h : Handlerˢ P A)
                      → T-alg-of-handlerᵀ bc h ∘ᵖ mapˣᵐ idᵖ (opᵀ {Tᵒ A ε''} {ε'} op)
                      ≈ᵖ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε' ε''))
                        ∘ᵖ h op (ε' ·ₑ ε'')
                        ∘ᵖ ⟨ fstᵐ
                           , ⟨ fstᵐ ∘ᵖ sndᵐ
                             ,   [ mapᵉ (op-grade op) ]ᶠ
                                   (map⇒ᵐ idᵖ (T-alg-of-handlerᵀ bc h) ∘ᵖ exp-strᵐ)
                               ∘ᵖ []-monoidal
                               ∘ᵖ mapˣᵐ (BoxCoalg.necᵉ bc {mapᵉ (op-grade op)}) idᵖ
                               ∘ᵖ ⟨ fstᵐ , sndᵐ ∘ᵖ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ
T-alg-of-handlerᵀ-opᵀ op bc h (pv , (v , boxk)) =
  ε-substˢ-congᵗ (sym (·ₑ-assoc (op-grade op) _ _))
    (app-cong (h op _)
      (≈-refl _ ,
       (≈-refl ⟦ param op ⟧ᵍ ,
        (λ q p y → T-alg-of-handlerˢ-cong bc h
                     (fun-nat (app (BoxCoalg.necᵉ bc) pv) q p)
                     (fun-nat boxk q p ⊑-refl y)))))

-- The fold commutes with sub-effecting: both sides put a `sub` node on top of
-- the folded tree (the fold's own `sub` clause *is* `T-≤`), so this holds on
-- the nose.

T-alg-of-handlerᵀ-≤ : ∀ {P A ε₁ ε₂ ε'} → (bc : BoxCoalg P) → (h : Handlerˢ P A) → (p : ε₁ ≾ₑ ε₂)
                    → T-alg-of-handlerᵀ {P} {A} {ε₂} {ε'} bc h ∘ᵖ mapˣᵐ idᵖ (T-≤ p)
                    ≈ᵖ T-≤ (·ₑ-monoˡ-≾ₑ p) ∘ᵖ T-alg-of-handlerᵀ {P} {A} {ε₁} {ε'} bc h
T-alg-of-handlerᵀ-≤ bc h p x = ≈ᵗ-refl _

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
