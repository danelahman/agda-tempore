------------------------------------------------------------------------
-- Effect handling: the parameterised fold and its (co)naturality.     --
--                                                                    --
-- `T-alg-of-handlerˢ` folds a handler over a computation tree, carrying --
-- an eternal parameter `P` (a `Eternalᵒ`, crossing locks via `necᵉ`),  --
-- with its two one-sided congruences and joint world-naturality.       --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.GroundTypes
import DenotationalSemantics.Model.Example.PSh.Base as B
import DenotationalSemantics.Model.Example.PSh.Modality.Future as F

module DenotationalSemantics.Model.Example.PSh.Monad.Handling.Core
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax)

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

open import DenotationalSemantics.Model.Example.PSh.Modality.Past Grades Wld using (PShPast)
open import DenotationalSemantics.Model.Example.PSh.Modality.Adjunction Grades Wld using (PShAdj)
open import DenotationalSemantics.Model.Modality.Eternal
  PShCat (GradeSystem.RGrade Grades) PShFut PShPast PShAdj

-- A handler parameterised by an eternal object `P`: a clause morphism for
-- every operation and residual grade, closing over `P`.

-- A handler bundles its clauses with a proof that they are *ambivalent* in the
-- residual grade `ε''`: clauses whose boxed continuations agree up to a
-- coercion `q` produce results agreeing up to `·ₑ-monoʳ-≾ₑ q`. The clause family
-- alone would not determine this — clauses at different `ε''` are a priori
-- unrelated morphisms — and it is exactly what the `sub-op` rule of `_≈ᵗ_`
-- needs to be respected by the fold (a coercion pushed under an operation
-- changes which clause is selected).
--
-- The witness is stated pointwise on *related boxes* rather than as a
-- reindexing equation, because that is the form the fold consumes: at a
-- `sub-op` node the two boxes differ by the fold's own `sub` clause, hence
-- agree definitionally.

-- The clause family alone, and the ambivalence property on it. The property is
-- stated as a *reindexing equation* (coercing the boxed continuation's residual
-- equals coercing the clause's output), which is the form expressible in an
-- arbitrary category — see the abstract `Handlerᵀ`.

Clausesˢ : PSh → PSh → Set
Clausesˢ P A = (op : Op) → (ε'' : E)
             → P ×ᵖ (⟦ param op ⟧ᵍ ×ᵖ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A ε''))
                 →ᵖ Tᵒ A (op-grade op ·ₑ ε'')

Monoˢ : ∀ {P A} → Clausesˢ P A → Set
Monoˢ {P} {A} cl = ∀ (op : Op) {εa εb} → (q : εa ≾ₑ εb)
                 → cl op εb ∘ᵖ mapˣᵐ idᵖ (mapˣᵐ idᵖ
                       ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵖ (T-≤ q))))
                 ≈ᵖ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵖ cl op εa

Handlerˢ : PSh → PSh → Set
Handlerˢ P A = Σ[ cl ∈ Clausesˢ P A ] Monoˢ cl

clause : ∀ {P A} → Handlerˢ P A → Clausesˢ P A
clause = proj₁

clause-mono′ : ∀ {P A} → (h : Handlerˢ P A) → Monoˢ (clause h)
clause-mono′ = proj₂

-- Reading the coerced box: `[ ρ ]ᶠ (map⇒ᵐ idᵖ (T-≤ q))` post-composes each fibre
-- with `sub q`, up to the accessibility witness it is read at (`fun-irr`).

coerced-box-fun : ∀ {A B ρ εa εb w w' w''} → (q : εa ≾ₑ εb)
                → (bx : carrier ([ ρ ]ᵒ (A ⇒ᵖ Tᵒ B εa)) w)
                → (r : w ⊑[ ρ ] w') → (s : w' ⊑[ uᵣ ] w'') → (y : carrier A w'')
                → fun (fun (app ([ ρ ]ᶠ (map⇒ᵐ idᵖ (T-≤ q))) bx) r) s y
                ≈ᵗ sub q (fun (fun bx r) s y)
coerced-box-fun q bx r s y = sub-≈ (fun-irr (fun bx r) _ s y)

-- The ambivalence property in the *pointwise* form the fold consumes: clauses
-- applied to boxes that agree up to a coercion `q` agree up to `·ₑ-monoʳ-≾ₑ q`.
-- Derived from the reindexing form by rewriting the coerced box.

clause-mono : ∀ {P A} → (h : Handlerˢ P A)
            → ∀ (op : Op) {εa εb w} → (q : εa ≾ₑ εb)
            → (pv : carrier P w) → (v : carrier ⟦ param op ⟧ᵍ w)
            → (bx  : carrier ([ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A εa)) w)
            → (bx' : carrier ([ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A εb)) w)
            → (∀ {w'} (r : w ⊑[ mapᵉ (op-grade op) ] w') {w''} (s : w' ⊑[ uᵣ ] w'')
                 (y : carrier ⟦ arity op ⟧ᵍ w'')
               → fun (fun bx' r) s y ≈ᵗ sub q (fun (fun bx r) s y))
            → app (clause h op εb) (pv , (v , bx'))
            ≈ᵗ sub (·ₑ-monoʳ-≾ₑ q) (app (clause h op εa) (pv , (v , bx)))
clause-mono {P} h op {εa} q pv v bx bx' rel =
  ≈ᵗ-trans
    (app-cong (clause h op _)
      (≈-refl P ,
       (≈-refl ⟦ param op ⟧ᵍ ,
        (λ r s y → ≈ᵗ-trans (rel r s y)
                     (≈ᵗ-sym (coerced-box-fun q bx r s y))))))
    (clause-mono′ h op q (pv , (v , bx)))

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

  T-alg-of-handlerˢ : ∀ {P A ε ε' w} → Eternalᵒ P → Handlerˢ P A
                    → carrier P w → Tˢ (Tᵒ A ε') ε w → Tˢ A (ε ·ₑ ε') w
  T-alg-of-handlerˢ {ε' = ε'} bc h pv (leaf s) =
    ε-substˢ (sym (·ₑ-identityˡ ε')) s
  T-alg-of-handlerˢ {ε' = ε'} bc h pv (op-node {ε = ε₀} op v k kc kn) =
    ε-substˢ (sym (·ₑ-assoc (op-grade op) ε₀ ε'))
      (app (clause h op (ε₀ ·ₑ ε')) (pv , (v , handler-box bc pv h op k kc kn)))
  T-alg-of-handlerˢ {ε' = ε'} bc h pv (delay-node {ε = ε₀} τ k kn) =
    ε-substˢ (sym (·ₑ-assoc (of-natᵉ τ) ε₀ ε'))
      (delay-node τ (λ q → T-alg-of-handlerˢ bc h (fun (app (Eternalᵒ.necᵉ bc) pv) q) (k q))
        (λ q r → ≈ᵗ-trans
          (T-alg-of-handlerˢ-congᵖ bc h (fun-nat (app (Eternalᵒ.necᵉ bc) pv) q r) (k (⊑ρ∘ᵘ q r)))
          (≈ᵗ-trans
            (T-alg-of-handlerˢ-congᵗ bc h _ (kn q r))
            (T-alg-of-handlerˢ-nat bc h r (fun (app (Eternalᵒ.necᵉ bc) pv) q) (k q)))))
  T-alg-of-handlerˢ bc h pv (sub p t) =
    sub (·ₑ-monoˡ-≾ₑ p) (T-alg-of-handlerˢ bc h pv t)

  -- The clause's boxed continuation, folded and rebundled. The eternal
  -- parameter `pv` is carried into the folded sub-computations at each future
  -- world via `necᵉ` (which crosses the operation's box `[ mapᵉ (op-grade op) ]`).

  handler-box : ∀ {P A ε₀ ε' w} (bc : Eternalᵒ P) (pv : carrier P w) (h : Handlerˢ P A) (op : Op)
      → (k : ∀ {w'} → w ⊑[ mapᵉ (op-grade op) ] w' → carrier ⟦ arity op ⟧ᵍ w'
           → Tˢ (Tᵒ A ε') ε₀ w')
      → (kc : ∀ {w'} (q : w ⊑[ mapᵉ (op-grade op) ] w')
                {y y' : carrier ⟦ arity op ⟧ᵍ w'}
            → _≈_ ⟦ arity op ⟧ᵍ y y' → k q y ≈ᵗ k q y')
      → (kn : ∀ {w' w''} (q : w ⊑[ mapᵉ (op-grade op) ] w') (r : w' ⊑[ uᵣ ] w'')
                (y : carrier ⟦ arity op ⟧ᵍ w')
            → k (⊑ρ∘ᵘ q r) (transport ⟦ arity op ⟧ᵍ r y) ≈ᵗ transportᵗ r (k q y))
      → [ mapᵉ (op-grade op) ]ᶜ (⟦ arity op ⟧ᵍ ⇒ᵖ Tᵒ A (ε₀ ·ₑ ε')) w
  handler-box {P = P} bc pv h op k kc kn = mk[]
    (λ q → mk⇒
      (λ r y → T-alg-of-handlerˢ bc h (fun (app (Eternalᵒ.necᵉ bc) pv) (⊑ρ∘ᵘ q r)) (k (⊑ρ∘ᵘ q r) y))
      (λ r e → T-alg-of-handlerˢ-congᵗ bc h _ (kc (⊑ρ∘ᵘ q r) e))
      (λ r s y → ≈ᵗ-trans
        (T-alg-of-handlerˢ-congᵖ bc h
          (≈-trans P ([]-fun-irr (app (Eternalᵒ.necᵉ bc) pv) _ _)
                     (fun-nat (app (Eternalᵒ.necᵉ bc) pv) (⊑ρ∘ᵘ q r) s))
          (k (⊑ρ∘ᵘ q (⊑ᵘ-trans r s)) (transport ⟦ arity op ⟧ᵍ s y)))
        (≈ᵗ-trans
          (T-alg-of-handlerˢ-congᵗ bc h _
            (≈ᵗ-trans
              (≡→≈ᵗ (cong (λ z → k z (transport ⟦ arity op ⟧ᵍ s y)) (⊑-irrelevant _ _)))
              (kn (⊑ρ∘ᵘ q r) s y)))
          (T-alg-of-handlerˢ-nat bc h s
            (fun (app (Eternalᵒ.necᵉ bc) pv) (⊑ρ∘ᵘ q r)) (k (⊑ρ∘ᵘ q r) y)))))
    (λ q r p y → ≈ᵗ-trans
                   (T-alg-of-handlerˢ-congᵖ bc h
                     ([]-fun-irr (app (Eternalᵒ.necᵉ bc) pv) _ _)
                     (k (⊑ρ∘ᵘ (⊑ρ∘ᵘ q r) p) y))
                   (T-alg-of-handlerˢ-congᵗ bc h _
                     (≡→≈ᵗ (cong (λ z → k z y) (⊑-irrelevant _ _)))))

  -- Congruence in the *tree* argument (the eternal parameter `pv` held fixed).

  T-alg-of-handlerˢ-congᵗ : ∀ {P A ε ε' w} (bc : Eternalᵒ P) (h : Handlerˢ P A)
                            (pv : carrier P w) {t t' : Tˢ (Tᵒ A ε') ε w}
                          → t ≈ᵗ t' → T-alg-of-handlerˢ bc h pv t ≈ᵗ T-alg-of-handlerˢ bc h pv t'
  T-alg-of-handlerˢ-congᵗ bc h pv (leaf-≈ e)             = ε-substˢ-congᵗ _ e
  T-alg-of-handlerˢ-congᵗ {P = P} bc h pv (op-≈ {op = op} ev ek) =
    ε-substˢ-congᵗ _ (app-cong (clause h op _)
      (≈-refl P , (ev , (λ q p y → T-alg-of-handlerˢ-congᵗ bc h _ (ek (⊑ρ∘ᵘ q p) y)))))
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
  -- The `op` case: the coercion pushed under the operation changes which clause
  -- the fold selects, and `clause-mono` is what identifies the two. The two
  -- boxes it relates differ exactly by the fold's own `sub` clause, so the
  -- relatedness premise holds definitionally.
  T-alg-of-handlerˢ-congᵗ {P = P} {ε' = ε'} bc h pv
    (sub-op {ε = ε₁} {ε' = ε₁'} {op = op} {e = e} {v = v} {k = k} {kc = kc} {kn = kn}) =
    ≈ᵗ-trans
      (sub-ε-substᵗ (sym (·ₑ-assoc (op-grade op) ε₁ ε'))
                    (sym (·ₑ-assoc (op-grade op) ε₁' ε'))
                    (·ₑ-monoʳ-≾ₑ (·ₑ-monoˡ-≾ₑ e))
                    (·ₑ-monoˡ-≾ₑ (·ₑ-monoʳ-≾ₑ e))
                    _)
      (ε-substˢ-congᵗ _
        (≈ᵗ-trans
          (≈ᵗ-sym (clause-mono h op (·ₑ-monoˡ-≾ₑ e) pv v
                     (handler-box bc pv h op k kc kn)
                     (handler-box bc pv h op (λ q y → sub e (k q y))
                        (λ q ey → sub-≈ (kc q ey)) (λ q r y → sub-≈ (kn q r y)))
                     (λ r s y → ≈ᵗ-refl _)))
          -- the two boxes differ only in their coherence witnesses, which the
          -- box's `_≈_` does not see
          (app-cong (clause h op _)
            (≈-refl P , (≈-refl ⟦ param op ⟧ᵍ , (λ q r y → ≈ᵗ-refl _))))))
  T-alg-of-handlerˢ-congᵗ bc h pv (≈ᵗ-sym et)           =
    ≈ᵗ-sym (T-alg-of-handlerˢ-congᵗ bc h pv et)
  T-alg-of-handlerˢ-congᵗ bc h pv (≈ᵗ-trans et et')     =
    ≈ᵗ-trans (T-alg-of-handlerˢ-congᵗ bc h pv et) (T-alg-of-handlerˢ-congᵗ bc h pv et')

  -- Congruence in the eternal *parameter* argument (the tree held fixed).

  T-alg-of-handlerˢ-congᵖ : ∀ {P A ε ε' w} (bc : Eternalᵒ P) (h : Handlerˢ P A)
                            {pv pv' : carrier P w} → _≈_ P pv pv'
                          → (t : Tˢ (Tᵒ A ε') ε w)
                          → T-alg-of-handlerˢ bc h pv t ≈ᵗ T-alg-of-handlerˢ bc h pv' t
  T-alg-of-handlerˢ-congᵖ bc h ep (leaf s)               = ≈ᵗ-refl _
  T-alg-of-handlerˢ-congᵖ bc h ep (op-node op v k kc kn) =
    ε-substˢ-congᵗ _ (app-cong (clause h op _)
      (ep , (≈-refl ⟦ param op ⟧ᵍ ,
        (λ q r y → T-alg-of-handlerˢ-congᵖ bc h
                     (app-cong (Eternalᵒ.necᵉ bc) ep (⊑ρ∘ᵘ q r)) (k (⊑ρ∘ᵘ q r) y)))))
  T-alg-of-handlerˢ-congᵖ bc h ep (delay-node τ k kn)    =
    ε-substˢ-congᵗ _ (delay-≈
      (λ q → T-alg-of-handlerˢ-congᵖ bc h (app-cong (Eternalᵒ.necᵉ bc) ep q) (k q)))
  T-alg-of-handlerˢ-congᵖ bc h ep (sub p t)              =
    sub-≈ (T-alg-of-handlerˢ-congᵖ bc h ep t)

  -- Naturality: the fold commutes with a (unit-graded) transport, jointly in
  -- the eternal parameter and the tree.

  T-alg-of-handlerˢ-nat : ∀ {P A ε ε' w w'} (bc : Eternalᵒ P) (h : Handlerˢ P A)
                          (r : w ⊑[ uᵣ ] w') (pv : carrier P w)
                          (t : Tˢ (Tᵒ A ε') ε w)
                        → T-alg-of-handlerˢ bc h (transport P r pv) (transportᵗ r t)
                        ≈ᵗ transportᵗ r (T-alg-of-handlerˢ bc h pv t)
  T-alg-of-handlerˢ-nat bc h r pv (leaf s) =
    ≡→≈ᵗ (sym (transportᵗ-ε-substˢ r (sym (·ₑ-identityˡ _)) s))
  T-alg-of-handlerˢ-nat {P = P} bc h r pv (op-node {ε = ε₀} op v k kc kn) =
    ≈ᵗ-trans
      (ε-substˢ-congᵗ (sym (·ₑ-assoc (op-grade op) ε₀ _))
        (app-cong (clause h op _)
          (≈-refl P ,
           (≈-refl ⟦ param op ⟧ᵍ ,
            (λ q s y → ≈ᵗ-trans
              (T-alg-of-handlerˢ-congᵖ bc h
                (≈-trans P (nat (Eternalᵒ.necᵉ bc) r pv (⊑ρ∘ᵘ q s))
                           ([]-fun-irr (app (Eternalᵒ.necᵉ bc) pv) _ _))
                (k _ y))
              (T-alg-of-handlerˢ-congᵗ bc h _
                (≡→≈ᵗ (cong (λ z → k z y) (⊑-irrelevant _ _)))))))))
      (≈ᵗ-trans
        (ε-substˢ-congᵗ (sym (·ₑ-assoc (op-grade op) ε₀ _))
          (nat (clause h op _) r (pv , (v , handler-box bc pv h op k kc kn))))
        (≡→≈ᵗ (sym (transportᵗ-ε-substˢ r (sym (·ₑ-assoc (op-grade op) ε₀ _)) _))))
  T-alg-of-handlerˢ-nat bc h r pv (delay-node {ε = ε₀} τ k kn) =
    ≈ᵗ-trans
      (ε-substˢ-congᵗ (sym (·ₑ-assoc (of-natᵉ τ) ε₀ _))
        (delay-≈ (λ q → T-alg-of-handlerˢ-congᵖ bc h
                          (nat (Eternalᵒ.necᵉ bc) r pv q) (k (⊑ᵘ∘ρ r q)))))
      (≡→≈ᵗ (sym (transportᵗ-ε-substˢ r (sym (·ₑ-assoc (of-natᵉ τ) ε₀ _)) _)))
  T-alg-of-handlerˢ-nat bc h r pv (sub e t) =
    sub-≈ (T-alg-of-handlerˢ-nat bc h r pv t)

-- Joint congruence, assembled from the two one-sided congruences.

T-alg-of-handlerˢ-cong : ∀ {P A ε ε' w} (bc : Eternalᵒ P) (h : Handlerˢ P A)
                         {pv pv' : carrier P w} {t t' : Tˢ (Tᵒ A ε') ε w}
                       → _≈_ P pv pv' → t ≈ᵗ t'
                       → T-alg-of-handlerˢ bc h pv t ≈ᵗ T-alg-of-handlerˢ bc h pv' t'
T-alg-of-handlerˢ-cong bc h {pv} {t' = t'} ep et =
  ≈ᵗ-trans (T-alg-of-handlerˢ-congᵗ bc h pv et) (T-alg-of-handlerˢ-congᵖ bc h ep t')

T-alg-of-handlerᵀ : ∀ {P A ε ε'} → Eternalᵒ P → Handlerˢ P A
                  → P ×ᵖ Tᵒ (Tᵒ A ε') ε →ᵖ Tᵒ A (ε ·ₑ ε')
T-alg-of-handlerᵀ bc h =
  pmap
    (λ pt → T-alg-of-handlerˢ bc h (proj₁ pt) (proj₂ pt))
    (λ e → T-alg-of-handlerˢ-cong bc h (proj₁ e) (proj₂ e))
    (λ r pt → T-alg-of-handlerˢ-nat bc h r (proj₁ pt) (proj₂ pt))
