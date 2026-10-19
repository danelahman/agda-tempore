------------------------------------------------------------------------
-- Interpretation of the well-typed terms (values and computations).  --
--                                                                    --
-- A value `Γ ⊢V⦂ A` is a morphism `⟦ Γ ⟧ →ᵐ ⟦ A ⟧ᵛ`; a computation   --
-- `Γ ⊢C⦂ C` is `⟦ Γ ⟧ →ᵐ ⟦ C ⟧ᶜ`. Variables use the machinery of     --
-- `Interpretation.Variables`, the effectful formers the graded       --
-- monad, and the Fitch formers the adjunction. Subsumption           --
-- post-composes the coercion of its witness.                         --
--                                                                    --
-- `perform`'s parameter/arity are ground types, interpreted via the  --
-- coercion `⟦ type-of-gtype G ⟧ᵛ ≡ ⟦ G ⟧ᵍ` (`ty-gty`).               --
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

module DenotationalSemantics.Interpretation.Terms
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types S
open import Syntax.Contexts S
open import Syntax.Language S
open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ; []-congᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤; εᵘ)
open Adjunction Adj using (η⊣; ε⊣)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ; ⟨⊤⟩-η; ⟨⊤⟩-eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Comparisons S Cat Fut Pst Adj GTy Mon GE
  using (holdsᵐ; cmpᵐ)

-- The value-type interpretation of a ground type coincides with its
-- ground-type interpretation.

ty-gty : ∀ (G : GType) → ⟦ type-of-gtype G ⟧ᵛ ≡ ⟦ G ⟧ᵍ
ty-gty (Base b)     = refl
ty-gty Unit         = refl
ty-gty Bool         = refl
ty-gty Empty        = refl
ty-gty (G₁ |×|ᵍ G₂) = cong₂ _×ᵐ_ (ty-gty G₁) (ty-gty G₂)
ty-gty ([ ρ ]ᵍ G)   = cong (λ O → [ ρ ]ᵒ O) (ty-gty G)

-- Naturality of `×ᵐ-assoc⁻¹` in its third component, and commutation of
-- domain- and codomain-reindexing of an exponential. Both are needed to push a
-- continuation coercion through `⟦_⟧ʰᵗ`'s adapter.

×ᵐ-assoc⁻¹-nat³ : ∀ {A B C C'} → (h : C →ᵐ C')
               → ×ᵐ-assoc⁻¹ {A} {B} {C'} ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ h)
               ≈ᵐ mapˣᵐ idᵐ h ∘ᵐ ×ᵐ-assoc⁻¹ {A} {B} {C}
×ᵐ-assoc⁻¹-nat³ h = ≈ᵐ-trans lhs≈canon (≈ᵐ-sym rhs≈canon)
  where
    fm : fstᵐ ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ h) ≈ᵐ fstᵐ
    fm = ≈ᵐ-trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _)
    sm : sndᵐ ∘ᵐ mapˣᵐ idᵐ (mapˣᵐ idᵐ h) ≈ᵐ mapˣᵐ idᵐ h ∘ᵐ sndᵐ
    sm = ⟨⟩ᵐ-sndᵐ _ _
    fm' : fstᵐ ∘ᵐ mapˣᵐ idᵐ h ≈ᵐ fstᵐ
    fm' = ≈ᵐ-trans (⟨⟩ᵐ-fstᵐ _ _) (∘ᵐ-identityˡ _)
    sm' : sndᵐ ∘ᵐ mapˣᵐ idᵐ h ≈ᵐ h ∘ᵐ sndᵐ
    sm' = ⟨⟩ᵐ-sndᵐ _ _
    lhs≈canon =
      ≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
        (⟨ ≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
             (⟨ fm
              , ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                (≈ᵐ-trans (∘ᵐ-congʳ sm)
                (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ fm'))) ⟩ᵐ-cong)
         , ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
           (≈ᵐ-trans (∘ᵐ-congʳ sm)
           (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
           (≈ᵐ-trans (∘ᵐ-congˡ sm') (∘ᵐ-assoc _ _ _)))) ⟩ᵐ-cong)
    rhs≈canon =
      ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _) (⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)

map⇒ᵐ-swap : ∀ {A B C D} → (f : A →ᵐ B) → (g : C →ᵐ D)
           → map⇒ᵐ f idᵐ ∘ᵐ map⇒ᵐ idᵐ g ≈ᵐ map⇒ᵐ idᵐ g ∘ᵐ map⇒ᵐ f idᵐ
map⇒ᵐ-swap f g =
  ≈ᵐ-trans (map⇒ᵐ-curryᵐˡ f _)
  (≈ᵐ-trans (curryᵐ-cong
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
              (∘ᵐ-congʳ (∘ᵐ-congʳ
                (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                          (mapˣᵐ-cong (∘ᵐ-identityˡ _) (∘ᵐ-identityˡ _))))))))
            (≈ᵐ-sym (≈ᵐ-trans (map⇒ᵐ-curryᵐ g _)
                              (curryᵐ-cong (∘ᵐ-congʳ (∘ᵐ-identityˡ _))))))

-- The step of a primitive recursion at `T B ε`: the recursive call's result
-- sequenced with the step's body `n` exactly as `_⨟_` is interpreted, the
-- context reaching `n` through `⟨⊤⟩-η` as a handler clause's does, followed
-- by the sub-effecting that absorbs the iteration.

recℕ-stepᵗ : ∀ {X B ε}
           → ε ·ₑ ε ≾ₑ ε
           → ⟨ mapᵉ ε ⟩ᵒ (⟨ ⊤ᵣ ⟩ᵒ X ×ᵐ ℕᵐ) ×ᵐ B →ᵐ Tᵒ B ε
           → (X ×ᵐ ℕᵐ) ×ᵐ Tᵒ B ε →ᵐ Tᵒ B ε
recℕ-stepᵗ p n =
  T-≤ p ∘ᵐ μᵀ ∘ᵐ Tᶠ n ∘ᵐ strᵀ ∘ᵐ mapˣᵐ (η⊣ ∘ᵐ mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ

-- The step of a primitive recursion on lists, likewise; the barred part of the
-- context is the ambient one, the head and the tail sit beside it.

recL-stepᵗ : ∀ {X A B ε}
           → ε ·ₑ ε ≾ₑ ε
           → ⟨ mapᵉ ε ⟩ᵒ ((⟨ ⊤ᵣ ⟩ᵒ X ×ᵐ A) ×ᵐ Listᵐ A) ×ᵐ B →ᵐ Tᵒ B ε
           → ((X ×ᵐ A) ×ᵐ Listᵐ A) ×ᵐ Tᵒ B ε →ᵐ Tᵒ B ε
recL-stepᵗ p n =
  T-≤ p ∘ᵐ μᵀ ∘ᵐ Tᶠ n ∘ᵐ strᵀ ∘ᵐ mapˣᵐ (η⊣ ∘ᵐ mapˣᵐ (mapˣᵐ ⟨⊤⟩-η idᵐ) idᵐ) idᵐ

-- The interpretation is defined only for *parametric* terms: a term whose
-- handlers are uniform in the residual effect grade the clauses are quantified
-- over. `Paramᶜ`/`Paramᵛ` is that certificate, and it is defined simultaneously
-- with the interpretation (induction-recursion) because the handler case has to
-- speak about the *denotations* of the clauses.
--
-- Every case but `handle` is inert, just collecting the sub-terms' certificates.

mutual

  Paramᵛ : ∀ {Γ A} → Γ ⊢V⦂ A → Set
  Paramᵛ (var f x)  = ⊤
  Paramᵛ (const c)  = ⊤
  Paramᵛ ⋆          = ⊤
  Paramᵛ true       = ⊤
  Paramᵛ false      = ⊤
  Paramᵛ zero       = ⊤
  Paramᵛ (succ V)   = Paramᵛ V
  Paramᵛ nil        = ⊤
  Paramᵛ (cons V W) = Paramᵛ V × Paramᵛ W
  Paramᵛ ⦉ V , W ⦊  = Paramᵛ V × Paramᵛ W
  Paramᵛ (inl V)    = Paramᵛ V
  Paramᵛ (inr V)    = Paramᵛ V
  Paramᵛ (lam M)    = Paramᶜ M
  Paramᵛ (subV V p) = Paramᵛ V

  Paramᶜ : ∀ {Γ C} → Γ ⊢C⦂ C → Set
  Paramᶜ (return V)       = Paramᵛ V
  Paramᶜ (M ⨟ N)          = Paramᶜ M × Paramᶜ N
  Paramᶜ (V · W)          = Paramᵛ V × Paramᵛ W
  Paramᶜ (match V `in M)  = Paramᵛ V × Paramᶜ M
  Paramᶜ (absurd V)       = Paramᵛ V
  Paramᶜ (cmp ⋈ V W et)   = Paramᵛ V × Paramᵛ W
  Paramᶜ (if V `then M `else N) = Paramᵛ V × Paramᶜ M × Paramᶜ N
  Paramᶜ (caseℕ V `zero M `succ N) = Paramᵛ V × Paramᶜ M × Paramᶜ N
  Paramᶜ (recℕ V M N p) = Paramᵛ V × Paramᶜ M × Paramᶜ N
  Paramᶜ (caseL V `nil M `cons N) = Paramᵛ V × Paramᶜ M × Paramᶜ N
  Paramᶜ (recL V M N p) = Paramᵛ V × Paramᶜ M × Paramᶜ N
  Paramᶜ (case+ V `inl M `inr N) = Paramᵛ V × Paramᶜ M × Paramᶜ N
  Paramᶜ (perform op V M) = Paramᵛ V × Paramᶜ M
  Paramᶜ (delay τ M)      = Paramᶜ M
  Paramᶜ (unbox x rel p M) = Paramᶜ M
  Paramᶜ (box _ V M)        = Paramᵛ V × Paramᶜ M
  Paramᶜ (subC M p)       = Paramᶜ M
  -- the handled computation, the return clause, every operation clause, and —
  -- the actual content — the clauses' uniformity in the residual grade
  Paramᶜ {Γ} (handle_`with_`in {B = B} M H N) =
    Paramᶜ M × Paramᶜ N ×
    Σ[ pH ∈ (∀ op ε'' → Paramᶜ (H op ε'')) ]
      EffUniformʰ {Γ} {B} H pH

  -- Naturality of a handler's clauses in the residual effect `ε''`: the clause
  -- commutes with sub-effecting the boxed continuation's residual, landing on
  -- `·ₑ-monoʳ`. This is what `Paramᶜ` carries for a `handle` and what becomes
  -- the semantic handler's `Monoᵀ` field (built by `⟦_⟧ʰᵗ`).
  EffUniformʰ : ∀ {Γ B}
              → (H : (op : Op) → (ε'' : E)
                   → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                     ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
              → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
              → Set
  EffUniformʰ H pH = ∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'')
               → ⟦ H op ε₂'' ⟧ᶜᵗ (pH op ε₂'')
                   ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
               ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H op ε₁'' ⟧ᶜᵗ (pH op ε₁'')

  ⟦_⟧ᵛᵗ : ∀ {Γ A} → (V : Γ ⊢V⦂ A) → Paramᵛ V → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ
  ⟦ var f x  ⟧ᵛᵗ _ = var-morphism f x
  ⟦ const c  ⟧ᵛᵗ _ = ⟦ c ⟧ᵇᶜ ∘ᵐ terminalᵐ
  ⟦ ⋆        ⟧ᵛᵗ _ = terminalᵐ
  ⟦ true     ⟧ᵛᵗ _ = trueᵐ ∘ᵐ terminalᵐ
  ⟦ false    ⟧ᵛᵗ _ = falseᵐ ∘ᵐ terminalᵐ
  ⟦ zero     ⟧ᵛᵗ _ = zeroᵐ ∘ᵐ terminalᵐ
  ⟦ succ V   ⟧ᵛᵗ pV = succᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ pV
  ⟦ nil      ⟧ᵛᵗ _ = nilᵐ ∘ᵐ terminalᵐ
  ⟦ cons V W ⟧ᵛᵗ (pV , pW) = consᵐ ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ pV , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
  ⟦ ⦉ V , W ⦊ ⟧ᵛᵗ (pV , pW) = ⟨ ⟦ V ⟧ᵛᵗ pV , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
  ⟦ inl V    ⟧ᵛᵗ pV = inlᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ pV
  ⟦ inr V    ⟧ᵛᵗ pV = inrᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ pV
  ⟦ lam M    ⟧ᵛᵗ pM = curryᵐ (⟦ M ⟧ᶜᵗ pM)
  ⟦ subV V p ⟧ᵛᵗ pV = ⟦ p ⟧<:ᵛ ∘ᵐ ⟦ V ⟧ᵛᵗ pV

  ⟦_⟧ᶜᵗ : ∀ {Γ C} → (M : Γ ⊢C⦂ C) → Paramᶜ M → ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ C ⟧ᶜ
  ⟦ return V ⟧ᶜᵗ pV = ηᵀ ∘ᵐ ⟦ V ⟧ᵛᵗ pV
  ⟦ _⨟_ {ε = ε} M N ⟧ᶜᵗ (pM , pN) =
    μᵀ ∘ᵐ Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ
  ⟦ V · W    ⟧ᶜᵗ (pV , pW) = appᵐ ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ pV , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
  ⟦ match V `in M ⟧ᶜᵗ (pV , pM) =
    ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ ⟨ idᵐ , fstᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ pV ⟩ᵐ , sndᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ pV ⟩ᵐ
  ⟦ absurd V ⟧ᶜᵗ pV = initialᵐ ∘ᵐ ⟦ V ⟧ᵛᵗ pV
  -- the relation's truth on the comparison of the operands
  ⟦ cmp ⋈ V W et ⟧ᶜᵗ (pV , pW) =
    ηᵀ ∘ᵐ holdsᵐ ⋈ ∘ᵐ cmpᵐ et ∘ᵐ ⟨ ⟦ V ⟧ᵛᵗ pV , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
  ⟦ if V `then M `else N ⟧ᶜᵗ (pV , pM , pN) =
    ifᵐ (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  ⟦ caseℕ V `zero M `succ N ⟧ᶜᵗ (pV , pM , pN) =
    caseℕᵐ (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  -- primitive recursion at `T ⟦ B ⟧ ε`, from the scrutinee
  ⟦ recℕ V M N p ⟧ᶜᵗ (pV , pM , pN) =
    recℕᵐ (⟦ M ⟧ᶜᵗ pM) (recℕ-stepᵗ p (⟦ N ⟧ᶜᵗ pN)) ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ
  ⟦ caseL V `nil M `cons N ⟧ᶜᵗ (pV , pM , pN) =
    caseLᵐ (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  -- primitive recursion on lists at `T ⟦ B ⟧ ε`, from the scrutinee
  ⟦ recL V M N p ⟧ᶜᵗ (pV , pM , pN) =
    recLᵐ (⟦ M ⟧ᶜᵗ pM) (recL-stepᵗ p (⟦ N ⟧ᶜᵗ pN)) ∘ᵐ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ
  ⟦ case+ V `inl M `inr N ⟧ᶜᵗ (pV , pM , pN) =
    caseᵐ (⟦ V ⟧ᵛᵗ pV) (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
  ⟦_⟧ᶜᵗ {Γ} (perform {A} {ε} op V M) (pV , pM) =
    opᵀ op ∘ᵐ
      ⟨ subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV)
      , [ mapᵉ (op-grade op) ]ᶠ
          (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ ×ᵐ O) →ᵐ Tᵒ ⟦ A ⟧ᵛ ε)
                         (ty-gty (arity op)) (⟦ M ⟧ᶜᵗ pM)))
        ∘ᵐ η⊣ ⟩ᵐ
  ⟦ delay τ M ⟧ᶜᵗ pM = delayᵀ τ ∘ᵐ [ of-durʳ τ ]ᶠ (⟦ M ⟧ᶜᵗ pM) ∘ᵐ η⊣
  ⟦_⟧ᶜᵗ {Γ} (handle_`with_`in {A} {B} {ε} {ε'} M H N) (pM , pN , pH , uH) =
      T-alg-of-handlerᵀ (⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ) (⟦_⟧ʰᵗ {Γ} H pH uH)
    ∘ᵐ ⟨ ⟨⊤⟩-η , Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ ⟩ᵐ
  ⟦ unbox x rel p M ⟧ᶜᵗ pM =
    ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ idᵐ , ⟦ p ⟧<:ᵛ ∘ᵐ ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x ⟩ᵐ
  ⟦ box ρ V M ⟧ᶜᵗ (pV , pM) =
    ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ idᵐ , [ ρ ]ᶠ (⟦ V ⟧ᵛᵗ pV) ∘ᵐ η⊣ ⟩ᵐ
  ⟦ subC M p ⟧ᶜᵗ pM = ⟦ p ⟧<:ᶜ ∘ᵐ ⟦ M ⟧ᶜᵗ pM

  -- The semantic handler of a syntactic one. Each clause sees the ambient
  -- context barred by `⟨ ⊤ᵣ ⟩`, so it interprets to a morphism parameterised
  -- by `⟨ ⊤ᵣ ⟩ᵒ ⟦ Γ ⟧` — the free `⟨⊤⟩`-algebra, hence eternal in every model.
  -- The `ty-gty` coercions adapt the ground-type parameter/arity to their
  -- value-type interpretations, and `×ᵐ-assoc⁻¹` reassociates the parameter.
  -- The handler's ambivalence is the clauses' uniformity `uH`, transported
  -- along that adapter.
  ⟦_⟧ʰᵗ : ∀ {Γ B}
        → (H : (op : Op) → (ε'' : E)
             → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                  ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
               ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
        → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
        → EffUniformʰ {Γ} {B} H pH
        → Handlerᵀ ⟦ Γ ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ ⟦ B ⟧ᵛ
  ⟦_⟧ʰᵗ {Γ} {B} H pH uH =
      (λ op ε'' → ⟦ H op ε'' ⟧ᶜᵗ (pH op ε'')
                    ∘ᵐ mapˣᵐ
                         (mapˣᵐ idᵐ (subst (λ O → ⟦ param op ⟧ᵍ →ᵐ O)
                                           (sym (ty-gty (param op))) idᵐ))
                         ([ mapᵉ (op-grade op) ]ᶠ
                           (map⇒ᵐ (subst (λ O → O →ᵐ ⟦ arity op ⟧ᵍ)
                                         (sym (ty-gty (arity op))) idᵐ) idᵐ))
                    ∘ᵐ ×ᵐ-assoc⁻¹)
    , (λ op q →
        ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ
          (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
          (≈ᵐ-trans (∘ᵐ-congʳ (×ᵐ-assoc⁻¹-nat³ _))
          (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
          (≈ᵐ-trans (∘ᵐ-congˡ
            (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
            (≈ᵐ-trans (mapˣᵐ-cong (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
                        (≈ᵐ-trans (≈ᵐ-sym ([]-∘ᵐ _ _))
                        (≈ᵐ-trans ([]-congᶠ (map⇒ᵐ-swap _ _)) ([]-∘ᵐ _ _))))
                      (≈ᵐ-sym (mapˣᵐ-∘ _ _ _ _)))))
                    (∘ᵐ-assoc _ _ _))))))
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congˡ (uH op q))
                  (∘ᵐ-assoc _ _ _)))))


-- The syntactic grade coercion `ε-subst` denotes the monad's `ε-substᵀ`. It
-- carries no computational content, so it also transports a term's
-- parametricity certificate.

ε-substᴾ : ∀ {Γ A ε ε'} → (e : ε ≡ ε') → (M : Γ ⊢C⦂ A ‼ ε)
         → Paramᶜ M → Paramᶜ (ε-subst e M)
ε-substᴾ refl M p = p

sound-ε-subst : ∀ {Γ A ε ε'} → (e : ε ≡ ε') → (M : Γ ⊢C⦂ A ‼ ε) → (pM : Paramᶜ M)
              → ⟦ ε-subst e M ⟧ᶜᵗ (ε-substᴾ e M pM) ≈ᵐ ε-substᵀ e ∘ᵐ ⟦ M ⟧ᶜᵗ pM
sound-ε-subst refl M pM =
  ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-congˡ ε-substᵀ-refl) (∘ᵐ-identityˡ _))

-- Regrading along an equivalence of effects is a sub-effecting, so it denotes
-- the monad's `T-≤`, and the certificate is the term's own.

sound-ε-≃ : ∀ {Γ A ε ε'} → (e : ε ≃ₑ ε') → (M : Γ ⊢C⦂ A ‼ ε) → (pM : Paramᶜ M)
          → ⟦ ε-≃ e M ⟧ᶜᵗ pM ≈ᵐ T-≤ (proj₁ e) ∘ᵐ ⟦ M ⟧ᶜᵗ pM
sound-ε-≃ {A = A} e M pM =
  ∘ᵐ-congˡ (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (T-congᶠ (⟦⟧<:ᵛ-refl A)) T-idᵐ))
                     (∘ᵐ-identityˡ _))
