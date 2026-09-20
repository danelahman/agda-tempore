------------------------------------------------------------------------
-- The bisimulation, rule by rule.
------------------------------------------------------------------------

open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Relation.Nullary using (¬_)

open import Util.Equality

module OperationalSemantics.Adequacy.StateEquivalence.Bisimulation (Spec : LanguageSpec) where
open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.RenActions    Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec
open import Syntax.Terms.Transport       Spec
open import Syntax.Substitutions.Variables Spec
open import OperationalSemantics.Adequacy.GradedReach          Spec
open import Syntax.Substitutions.Equivalence Spec

open import OperationalSemantics.Adequacy.StateEquivalence.Core Spec
open import OperationalSemantics.Adequacy.StateEquivalence.Extensions Spec

-- `Sim es M' r` is what simulating `r` from the related configuration
-- amounts to: a state, a reduct, their relations, the step, and the fact
-- that the two steps extend the state alike.

Sim : ∀ {A ε ε₁} {St St' St₁ : 𝕊 []}
    → (es : St ≐ˢ St') → {M : toCtx St ⊢C⦂ A ‼ ε} → (M' : toCtx St' ⊢C⦂ A ‼ ε)
    → {N : toCtx St₁ ⊢C⦂ A ‼ ε₁} → (r : ⟨ St , M ⟩ ↝ ⟨ St₁ , N ⟩) → Set
Sim {A} {ε₁ = ε₁} {St' = St'} {St₁ = St₁} es M' {N} r =
  Σ[ St₁' ∈ 𝕊 [] ] Σ[ N' ∈ (toCtx St₁' ⊢C⦂ A ‼ ε₁) ] Σ[ es₁ ∈ St₁ ≐ˢ St₁' ]
  Σ[ r' ∈ (⟨ St' , M' ⟩ ↝ ⟨ St₁' , N' ⟩) ]
    (step-extends-state r ≤≐ step-extends-state r')
  × (N ≡ castᶜ (sym (toCtx-≐ˢ es₁)) N')

-- subsumption at a returned value: the coercion is absorbed by the value on
-- both sides, the two witnesses agreeing by `<:ᵛ-irrelevant`.

↝-≐ˢ-sub-ret : ∀ {A A' ε'} {St St' : 𝕊 []} → (es : St ≐ˢ St')
            → {V : toCtx St ⊢V⦂ A} → {p : A <:ᵛ A'} → {q : uₑ ≾ₑ ε'}
            → (P' : toCtx St' ⊢C⦂ A' ‼ ε')
            → subC (return V) (p ‼ₛ q) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
            → Sim es P' (SUB-RET {V = V} {p = p} {q = q})
↝-≐ˢ-sub-ret es {p = p} P' eM with cast-sub⁻ (sym (toCtx-≐ˢ es)) P' eM
... | p₁ ‼ₛ q₁ , M₀' , refl , eM₀
  with cast-return⁻ (sym (toCtx-≐ˢ es)) M₀' eM₀
...   | V' , refl , eV =
    _ , _ , es , SUB-RET , id-≤≐
  , trans (cong return (cong₂ subV eV (<:ᵛ-irrelevant p p₁)))
          (sym (trans (cast-ret (sym (toCtx-≐ˢ es)))
                      (cong return (cast-subV (sym (toCtx-≐ˢ es))))))

-- subsumption at a performed operation: it is pushed into the continuation on
-- both sides.

↝-≐ˢ-sub-op : ∀ {A A' ε ε'} {op : Op} {St St' : 𝕊 []} → (es : St ≐ˢ St')
           → {V : toCtx St ⊢V⦂ type-of-gtype (param op)}
           → {M₀ : toCtx St ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                     ⊢C⦂ A ‼ ε}
           → {p : A <:ᵛ A'} → {q : op-grade op ·ₑ ε ≾ₑ ε'}
           → (P' : toCtx St' ⊢C⦂ A' ‼ ε')
           → subC (perform op V M₀) (p ‼ₛ q) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
           → Sim es P' (SUB-OP {V = V} {M = M₀} {p = p} {q = q})
↝-≐ˢ-sub-op {op = op} es P' eM with cast-sub⁻ (sym (toCtx-≐ˢ es)) P' eM
... | p₁ ‼ₛ q₁ , M₁' , refl , eM₁
  with cast-perform⁻ (sym (toCtx-≐ˢ es)) M₁' eM₁
...   | V' , M₀' , refl , eV , eM₀ =
    _ , _ , es , SUB-OP , id-≤≐
  , trans (cong₂ (perform op) eV (cong₂ subC eM₀ (<:ᶜ-irrelevant _ _)))
          (sym (trans (cast-perform (sym (toCtx-≐ˢ es)))
                      (cong (perform op _) (cast-subC _))))

-- subsumption at an eliminated function: the coercion splits the same way on
-- both sides.

↝-≐ˢ-sub-app : ∀ {A A₁ B C₁ ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
            → {V : toCtx St ⊢V⦂ A₁ ⇒ C₁} → {W : toCtx St ⊢V⦂ A}
            → {q : A <:ᵛ A₁} → {r : C₁ <:ᶜ B ‼ ε}
            → (P' : toCtx St' ⊢C⦂ B ‼ ε)
            → (subV V (q ⇒ₛ r) · W) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
            → Sim es P' (SUB-APP {V = V} {W = W} {q = q} {r = r})
↝-≐ˢ-sub-app es {q = q} {r = r} P' eM
  with cast-app⁻ (sym (toCtx-≐ˢ es)) P' eM
... | Vf' , W' , refl , eVf , eW
  with cast-subV⁻ (sym (toCtx-≐ˢ es)) Vf' eVf
...   | q₁ ⇒ₛ r₁ , V' , refl , eV =
    _ , _ , es , SUB-APP , id-≤≐
  , trans (cong₂ subC (cong₂ _·_ eV (cong₂ subV eW (<:ᵛ-irrelevant q q₁)))
                      (<:ᶜ-irrelevant r r₁))
          (sym (trans (cast-subC (sym (toCtx-≐ˢ es)))
                 (cong (λ z → subC z r₁)
                   (trans (cast-app (sym (toCtx-≐ˢ es)))
                          (cong (_ ·_) (cast-subV (sym (toCtx-≐ˢ es))))))))

-- subsumption at a scrutinised boolean: `Boolₛ` is dropped on both sides.

↝-≐ˢ-sub-if : ∀ {A ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
           → {V : toCtx St ⊢V⦂ Bool} → {M N : toCtx St ⊢C⦂ A ‼ ε}
           → (P' : toCtx St' ⊢C⦂ A ‼ ε)
           → (if subV V Boolₛ `then M `else N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
           → Sim es P' (SUB-IF {V = V} {M = M} {N = N})
↝-≐ˢ-sub-if es P' eM with cast-if⁻ (sym (toCtx-≐ˢ es)) P' eM
... | Vb' , M₀' , N₀' , refl , eVb , eM₀ , eN₀
  with cast-subV⁻ (sym (toCtx-≐ˢ es)) Vb' eVb
...   | Boolₛ , V' , refl , eV =
    _ , _ , es , SUB-IF , id-≤≐
  , trans (cong₃ (λ v m n → if v `then m `else n) eV eM₀ eN₀)
          (sym (cast-if (sym (toCtx-≐ˢ es))))

-- subsumption elsewhere: step underneath it on both sides. The scrutinee's
-- simulation is passed in, as the recursion supplies it.

↝-≐ˢ-sub-step : ∀ {A A' ε ε' ε''} {St St' St₁ : 𝕊 []} → (es : St ≐ˢ St')
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M₁ : toCtx St₁ ⊢C⦂ A ‼ ε''}
             → (M' : toCtx St' ⊢C⦂ A ‼ ε)
             → (p : A <:ᵛ A') → (q : ε ≾ₑ ε')
             → (p₁ : A <:ᵛ A') → (q₁ : ε ≾ₑ ε')
             → (r : ⟨ St , M ⟩ ↝ ⟨ St₁ , M₁ ⟩)
             → Sim es M' r
             ----------------------------------------------------------
             → Sim es (subC M' (p₁ ‼ₛ q₁)) (SUB-STEP {p = p} {q = q} r)
↝-≐ˢ-sub-step es M' p q p₁ q₁ r (St₂' , M₂' , es₂ , r' , h , eM₂) =
    St₂' , _ , es₂ , SUB-STEP r' , h
  , trans (cong₂ subC eM₂ (<:ᶜ-irrelevant _ _))
          (sym (cast-subC (sym (toCtx-≐ˢ es₂))))

-- boolean elimination: the scrutinee is the same constant on both sides
-- (`cast-true⁻`/`cast-false⁻`), and the reduct is the branch it names.

↝-≐ˢ-if-true : ∀ {A ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
            → {M N : toCtx St ⊢C⦂ A ‼ ε}
            → (P' : toCtx St' ⊢C⦂ A ‼ ε)
            → (if true `then M `else N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
            → Sim es P' (IF-TRUE {M = M} {N = N})
↝-≐ˢ-if-true es P' eM with cast-if⁻ (sym (toCtx-≐ˢ es)) P' eM
... | V' , M₀' , N₀' , refl , eV , eM₀ , eN₀
      with cast-true⁻ (sym (toCtx-≐ˢ es)) V' eV
...     | refl = _ , _ , es , IF-TRUE , id-≤≐ , eM₀

↝-≐ˢ-if-false : ∀ {A ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
             → {M N : toCtx St ⊢C⦂ A ‼ ε}
             → (P' : toCtx St' ⊢C⦂ A ‼ ε)
             → (if false `then M `else N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
             → Sim es P' (IF-FALSE {M = M} {N = N})
↝-≐ˢ-if-false es P' eM with cast-if⁻ (sym (toCtx-≐ˢ es)) P' eM
... | V' , M₀' , N₀' , refl , eV , eM₀ , eN₀
      with cast-false⁻ (sym (toCtx-≐ˢ es)) V' eV
...     | refl = _ , _ , es , IF-FALSE , id-≤≐ , eN₀

-- application: the function is a lambda on both sides, and the reducts are the
-- same substitution (`sub-≡ᶜ`), the cast commuting with it (`cast-app-reduct`).

↝-≐ˢ-app : ∀ {A B ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
        → {M₀ : toCtx St ∷ A ⊢C⦂ B ‼ ε} → {V : toCtx St ⊢V⦂ A}
        → (P' : toCtx St' ⊢C⦂ B ‼ ε)
        → (lam M₀ · V) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
        → Sim es P' (APP {M = M₀} {V = V})
↝-≐ˢ-app es P' eM with cast-app⁻ (sym (toCtx-≐ˢ es)) P' eM
... | Vf' , W' , refl , eVf , eW with cast-lam⁻ (sym (toCtx-≐ˢ es)) Vf' eVf
...   | M₀' , refl , eM₀ =
    _ , _ , es , APP , id-≤≐
  , subst (λ z → _ ≡ z) (cast-app-reduct (sym (toCtx-≐ˢ es)) M₀' W')
          (sub-≡ᶜ split-[] eW eM₀)

-- a delay moves the lock into the state, so the two states are related by
-- `⟨⟩-≐ˢ` and the extensions by `⟨⟩-≤≐`

↝-≐ˢ-delay : ∀ {A ε τ} {St St' : 𝕊 []} → (es : St ≐ˢ St')
          → {M₀ : toCtx St ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε}
          → (P' : toCtx St' ⊢C⦂ A ‼ (of-natᵉ τ ·ₑ ε))
          → delay τ M₀ ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
          → Sim es P' (DELAY {M = M₀})
↝-≐ˢ-delay {τ = τ} es P' eM with cast-delay⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M₀' , refl , eM₀ =
    _ , _ , ⟨⟩-≐ˢ (of-natʳ τ) es , DELAY , ⟨⟩-≤≐ (of-natʳ τ) id-≤≐
  , subst (λ z → _ ≡ z) (castᶜ-irr _ _ M₀') eM₀

-- `box` allocates: the two states are related by `∷-≐ˢ` at the stored values
-- (`cast-box-val` moves the cast past the reindexing `_∷ₛ_` applies).

↝-≐ˢ-box : ∀ {A B ρ ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
        → {V : toCtx St ⟨ ρ ⟩ ⊢V⦂ A} → {M₀ : toCtx St ∷ [ ρ ] A ⊢C⦂ B ‼ ε}
        → (P' : toCtx St' ⊢C⦂ B ‼ ε)
        → box V M₀ ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
        → Sim es P' (BOX {V = V} {M = M₀})
↝-≐ˢ-box es P' eM with cast-box⁻ (sym (toCtx-≐ˢ es)) P' eM
... | V' , M₀' , refl , eV , eM₀ =
    _ , _
  , ∷-≐ˢ es (subst (λ z → _ ≡ z)
                   (cast-box-val (sym (toCtx-≐ˢ es)) V')
                   (V-rename-cong (eq-ren (sym ++ᶜ-identityˡ)) eV))
  , BOX , ∷-≤≐ id-≤≐
  , subst (λ z → _ ≡ z) (castᶜ-irr _ _ M₀') eM₀

-- matching: the scrutinee corresponds on both sides, and its two projections
-- commute with the cast (`fstᵛ-cast`/`sndᵛ-cast`).

↝-≐ˢ-match : ∀ {A B D ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
          → {U : toCtx St ⊢V⦂ A |×| B}
          → {M₀ : toCtx St ∷ A ∷ B ⊢C⦂ D ‼ ε}
          → (P' : toCtx St' ⊢C⦂ D ‼ ε)
          → (match U `in M₀) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
          → Sim es P' (MATCH {P = U} {M = M₀})
↝-≐ˢ-match es P' eM with cast-match⁻ (sym (toCtx-≐ˢ es)) P' eM
... | U' , M₀' , refl , eU , eM₀ =
    _ , _ , es , MATCH , id-≤≐
  , subst (λ z → _ ≡ z)
      (cast-match-reduct (sym (toCtx-≐ˢ es)) M₀' (fstᵛ U') (sndᵛ U'))
      (sub-≡ᶜ split-[]
        (trans (cong fstᵛ eU) (fstᵛ-cast (sym (toCtx-≐ˢ es)) U'))
        (sub-≡ᶜ split-[]
          (V-rename-cong wk-ren
            (trans (cong sndᵛ eU) (sndᵛ-cast (sym (toCtx-≐ˢ es)) U')))
          eM₀))

-- sequencing a returned value: the continuation is retyped by a renaming that
-- mentions the context, so `cast-seq-ret` is what moves the cast past it.

↝-≐ˢ-seq-ret : ∀ {A B ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
            → {V : toCtx St ⊢V⦂ A} → {N : toCtx St ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε}
            → (P' : toCtx St' ⊢C⦂ B ‼ (uₑ ·ₑ ε))
            → (return V ⨟ N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
            → Sim es P' (SEQ-RET {V = V} {N = N})
↝-≐ˢ-seq-ret es P' eM with cast-seq⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M₁' , N' , refl , eM₁ , eN with cast-return⁻ (sym (toCtx-≐ˢ es)) M₁' eM₁
...   | V' , refl , eV =
    _ , _ , es , SEQ-RET , id-≤≐
  , subst (λ z → _ ≡ z) (cast-seq-ret (sym (toCtx-≐ˢ es)) N' V')
      (sub-≡ᶜ split-[] eV (C-rename-cong (cong-∷-ren _) eN))

-- handling a returned value: as `SEQ-RET`, with the handler discarded.

↝-≐ˢ-handle-ret : ∀ {A B ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
               → {V : toCtx St ⊢V⦂ A}
               → {H : (op : Op) → (ε' : E) →
                        toCtx St ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                          ∷ [ mapᵉ (op-grade op) ]
                              (type-of-gtype (arity op) ⇒ B ‼ ε')
                        ⊢C⦂ B ‼ (op-grade op ·ₑ ε')}
               → {N : toCtx St ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε}
               → (P' : toCtx St' ⊢C⦂ B ‼ (uₑ ·ₑ ε))
               → (handle return V `with H `in N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
               → Sim es P' (HANDLE-RET {V = V} {H = H} {N = N})
↝-≐ˢ-handle-ret es P' eM with cast-handle⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M₁' , H' , N' , refl , eM₁ , eH , eN
  with cast-return⁻ (sym (toCtx-≐ˢ es)) M₁' eM₁
...   | V' , refl , eV =
    _ , _ , es , HANDLE-RET , id-≤≐
  , subst (λ z → _ ≡ z) (cast-seq-ret (sym (toCtx-≐ˢ es)) N' V')
      (sub-≡ᶜ split-[] eV (C-rename-cong (cong-∷-ren _) eN))

-- unboxing: the store is read at the same cell, so the substituted values are
-- related (`unbox-lookup-≐ˢ`).

↝-≐ˢ-unbox : ∀ {A A₀ D ε ρ ρ'} {St St' : 𝕊 []} → (es : St ≐ˢ St')
          → {x : [ ρ ] A₀ ∈[ ρ' ] toCtx St} → {rel : ρ' ≾ᵣ ρ} → {p : A₀ <:ᵛ A}
          → {M₀ : toCtx St ∷ A ⊢C⦂ D ‼ ε}
          → (P' : toCtx St' ⊢C⦂ D ‼ ε)
          → unbox x rel p M₀ ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
          → Sim es P' (UNBOX {z = x} {rel = rel} {p = p} {M = M₀})
↝-≐ˢ-unbox {St = St} {St' = St'} es {x = x} {rel = rel} {p = p} P' eM
  with cast-unbox⁻ (sym (toCtx-≐ˢ es)) P' eM
... | _ , x' , rel' , p' , M₀' , refl , hw , eM₀ =
    _ , _ , es , UNBOX , id-≤≐
  , subst (λ z → _ ≡ z)
      (cast-app-reduct (sym (toCtx-≐ˢ es)) M₀'
        (subV (unbox-lookup St' x' rel') p'))
      (sub-≡ᶜ split-[]
        (trans (cong₂ subV
                 (unbox-lookup-≐ˢ es {x = x} {x' = x'} {rel = rel} {rel' = rel'} hw)
                 (<:ᵛ-irrelevant p p'))
               (sym (cast-subV (sym (toCtx-≐ˢ es)))))
        eM₀)

-- sequencing an operation: the operation floats out, its continuation gaining
-- the sequel. The reduct is retyped in its *effect* (`ε-subst`) as well.

ε-subst-≡ : ∀ {Γ A ε ε'} → (e : ε ≡ ε') → {M M' : Γ ⊢C⦂ A ‼ ε}
          → M ≡ M' → ε-subst e M ≡ ε-subst e M'
ε-subst-≡ refl eM = eM

cast-seq-op : ∀ {Γ Γ' A B ε ε'} {op : Op} → (e : Γ' ≡ Γ)
            → (V' : Γ' ⊢V⦂ type-of-gtype (param op))
            → (M' : Γ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                      ⊢C⦂ A ‼ ε)
            → (N' : Γ' ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
            → ε-subst (sym (·ₑ-assoc (op-grade op) ε ε'))
                (perform op (castᵛ e V')
                  ((castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                          ∷ type-of-gtype (arity op)) e) M')
                    ⨟ C-rename
                        (cong-∷-ren ((eq-ren (cong (Γ ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren)
                                     ∘ʳ cong-⟨⟩-ren wk-ren))
                        (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A) e)
                               N')))
            ≡ castᶜ e
                (ε-subst (sym (·ₑ-assoc (op-grade op) ε ε'))
                  (perform op V'
                    (M' ⨟ C-rename
                            (cong-∷-ren ((eq-ren (cong (Γ' ⟨_⟩) map-·ᵉ)
                                          ∘ʳ ⟨⟩-μ-ren)
                                         ∘ʳ cong-⟨⟩-ren wk-ren))
                            N')))
cast-seq-op refl V' M' N' = refl

↝-≐ˢ-seq-op : ∀ {A B ε ε'} {op : Op} {St St' : 𝕊 []} → (es : St ≐ˢ St')
           → {V : toCtx St ⊢V⦂ type-of-gtype (param op)}
           → {M₀ : toCtx St ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                     ⊢C⦂ A ‼ ε}
           → {N : toCtx St ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε'}
           → (P' : toCtx St' ⊢C⦂ B ‼ ((op-grade op ·ₑ ε) ·ₑ ε'))
           → (perform op V M₀ ⨟ N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
           → Sim es P' (SEQ-OP {V = V} {M = M₀} {N = N})
↝-≐ˢ-seq-op es P' eM with cast-seq⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M₁' , N' , refl , eM₁ , eN
  with cast-perform⁻ (sym (toCtx-≐ˢ es)) M₁' eM₁
...   | V' , M₀' , refl , eV , eM₀ =
    _ , _ , es , SEQ-OP , id-≤≐
  , subst (λ z → _ ≡ z) (cast-seq-op (sym (toCtx-≐ˢ es)) V' M₀' N')
      (ε-subst-≡ _
        (cong₂ (perform _) eV (cong₂ _⨟_ eM₀ (C-rename-cong (cong-∷-ren _) eN))))

cast-rename-∷ : ∀ {Γ₁ Γ₂ Γ₁' Γ₂' A C} → (e₁ : Γ₁' ≡ Γ₁) → (e₂ : Γ₂' ≡ Γ₂)
              → (r' : Ren [] Γ₂' Γ₁') → (M' : Γ₁' ∷ A ⊢C⦂ C)
              → C-rename (cong-∷-ren (castʳ² e₁ e₂ r'))
                  (castᶜ (cong (_∷ A) e₁) M')
              ≡ castᶜ (cong (_∷ A) e₂) (C-rename (cong-∷-ren r') M')
cast-rename-∷ refl refl r' M' = refl

-- The same for a clause: `HANDLE-STEP` retypes it by a renaming under the
-- barrier and the clause's two binders.

cast-rename-cl : ∀ {Γ₁ Γ₂ Γ₁' Γ₂' A A₀ C} → (e₁ : Γ₁' ≡ Γ₁) → (e₂ : Γ₂' ≡ Γ₂)
               → (r' : Ren [] (Γ₂' ⟨ ⊤ᵣ ⟩) (Γ₁' ⟨ ⊤ᵣ ⟩))
               → (M' : Γ₁' ⟨ ⊤ᵣ ⟩ ∷ A ∷ A₀ ⊢C⦂ C)
               → C-rename (cong-∷-ren (cong-∷-ren
                   (castʳ² (cong (_⟨ ⊤ᵣ ⟩) e₁) (cong (_⟨ ⊤ᵣ ⟩) e₂) r')))
                   (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ⊤ᵣ ⟩ ∷ A ∷ A₀) e₁) M')
               ≡ castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ⊤ᵣ ⟩ ∷ A ∷ A₀) e₂)
                   (C-rename (cong-∷-ren (cong-∷-ren r')) M')
cast-rename-cl refl refl r' M' = refl

-- `HANDLE-OP`'s reduct in one lemma: the cast moves past the box, the lambda,
-- the inner handle, the three renamings and the substitution of the parameter.
-- The fired clause crosses the barrier by a renaming, so nothing is retyped.

cast-handle-op : ∀ {Γ Γ' A B ε ε''} {op : Op} → (e : Γ' ≡ Γ)
               → (V' : Γ' ⊢V⦂ type-of-gtype (param op))
               → (M' : Γ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                         ⊢C⦂ A ‼ ε)
               → (H' : (op' : Op) → (ε' : E) →
                         Γ' ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op')
                           ∷ [ mapᵉ (op-grade op') ]
                               (type-of-gtype (arity op') ⇒ B ‼ ε')
                         ⊢C⦂ B ‼ (op-grade op' ·ₑ ε'))
               → (N' : Γ' ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε'')
               → box (lam
                       (handle (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                                      ∷ type-of-gtype (arity op))
                                            e) M')
                       `with (λ op' ε' →
                                C-rename
                                  (cong-∷-ren (cong-∷-ren
                                    (barrier-wk-ren (mapᵉ (op-grade op))
                                                    (type-of-gtype (arity op)))))
                                  (castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ⊤ᵣ ⟩
                                                         ∷ type-of-gtype (param op')
                                                         ∷ [ mapᵉ (op-grade op') ]
                                                             (type-of-gtype (arity op')
                                                                ⇒ B ‼ ε'))
                                               e)
                                         (H' op' ε')))
                       `in (C-rename
                             (  cong-∷-ren ((eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)
                             ∘ʳ ⟨⟩-μ-ren)
                             ∘ʳ cong-⟨⟩-ren wk-ren))
                             (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A)
                                          e) N'))))
                      (C-rename (cong-∷-ren (cong-∷-ren barrier-ren))
                        (castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                                               ∷ [ mapᵉ (op-grade op) ]
                                                   (type-of-gtype (arity op)
                                                      ⇒ B ‼ (ε ·ₑ ε'')))
                                     e)
                               (H' op (ε ·ₑ ε'')))
                       [ split-∷ split-[] ↦ castᵛ e V' ]c)
               ≡ castᶜ e
                   (box (lam
                          (handle M'
                          `with (λ op' ε' →
                                   C-rename
                                     (cong-∷-ren (cong-∷-ren
                                       (barrier-wk-ren (mapᵉ (op-grade op))
                                                       (type-of-gtype (arity op)))))
                                     (H' op' ε'))
                          `in (C-rename
                                (  cong-∷-ren ((eq-ren (cong (Γ' ⟨_⟩) map-·ᵉ)
                                ∘ʳ ⟨⟩-μ-ren)
                                ∘ʳ cong-⟨⟩-ren wk-ren))
                                N')))
                         (C-rename (cong-∷-ren (cong-∷-ren barrier-ren))
                                   (H' op (ε ·ₑ ε''))
                          [ split-∷ split-[] ↦ V' ]c))
cast-handle-op refl V' M' H' N' = refl

-- `HANDLE-OP` fires a clause: the state is unchanged, and every piece of the
-- reduct is a congruence for `_≡_`.

↝-≐ˢ-handle-op : ∀ {A B ε ε''} {op : Op} {St St' : 𝕊 []} → (es : St ≐ˢ St')
              → {V : toCtx St ⊢V⦂ type-of-gtype (param op)}
              → {M₀ : toCtx St ⟨ mapᵉ (op-grade op) ⟩
                        ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
              → {H : (op' : Op) → (ε' : E) →
                       toCtx St ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op')
                         ∷ [ mapᵉ (op-grade op') ]
                             (type-of-gtype (arity op') ⇒ B ‼ ε')
                       ⊢C⦂ B ‼ (op-grade op' ·ₑ ε')}
              → {N : toCtx St ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε''}
              → (P' : toCtx St' ⊢C⦂ B ‼ ((op-grade op ·ₑ ε) ·ₑ ε''))
              → (handle perform op V M₀ `with H `in N)
                  ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
              → Sim es P' (HANDLE-OP {V = V} {M = M₀} {H = H} {N = N})

↝-≐ˢ-handle-op {A = A} {B = B} {ε = ε} {ε'' = ε''} {op = op} {St = St} {St' = St'}
              es P' eM
  with cast-handle⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M₁' , H' , N' , refl , eM₁ , eH , eN
  with cast-perform⁻ (sym (toCtx-≐ˢ es)) M₁' eM₁
...   | V' , M₀' , refl , eV , eM₀ =
    _ , _ , es , HANDLE-OP , id-≤≐
  , subst (λ z → _ ≡ z)
      (cast-handle-op (sym (toCtx-≐ˢ es)) V' M₀' H' N')
      (cong₂ box
        (cong lam
          (handle-≡ eM₀
            (λ op' ε' →
               C-rename-cong (cong-∷-ren (cong-∷-ren
                               (barrier-wk-ren (mapᵉ (op-grade op))
                                               (type-of-gtype (arity op)))))
                             (eH op' ε'))
            (C-rename-cong (cong-∷-ren _) eN)))
        (sub-≡ᶜ (split-∷ split-[]) eV
          (C-rename-cong (cong-∷-ren (cong-∷-ren barrier-ren))
                         (eH op (ε ·ₑ ε'')))))

-- `HANDLE-STEP`: as `SEQ-STEP`, plus the clause retyping. The scrutinee's
-- simulation is passed in, as the recursion supplies it.

↝-≐ˢ-handle-step : ∀ {A B ε₁ ε₂ ε₁'} {St St' St₁ : 𝕊 []} → (es : St ≐ˢ St')
                → {M : toCtx St ⊢C⦂ A ‼ ε₁}
                → {H : (op : Op) → (ε₃ : E) →
                         toCtx St ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                           ∷ [ mapᵉ (op-grade op) ]
                               (type-of-gtype (arity op) ⇒ B ‼ ε₃)
                         ⊢C⦂ B ‼ (op-grade op ·ₑ ε₃)}
                → {N : toCtx St ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂}
                → {M₁ : toCtx St₁ ⊢C⦂ A ‼ ε₁'}
                → (M' : toCtx St' ⊢C⦂ A ‼ ε₁)
                → (H' : (op : Op) → (ε₃ : E) →
                          toCtx St' ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                            ∷ [ mapᵉ (op-grade op) ]
                                (type-of-gtype (arity op) ⇒ B ‼ ε₃)
                          ⊢C⦂ B ‼ (op-grade op ·ₑ ε₃))
                → (N' : toCtx St' ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
                → (∀ op ε₃ → H op ε₃
                     ≡ castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                                              ∷ [ mapᵉ (op-grade op) ]
                                                  (type-of-gtype (arity op) ⇒ B ‼ ε₃))
                               (sym (toCtx-≐ˢ es)))
                              (H' op ε₃))
                → N ≡ castᶜ (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε₁ ⟩ ∷ A) (sym (toCtx-≐ˢ es))) N'
                → (r : ⟨ St , M ⟩ ↝ ⟨ St₁ , M₁ ⟩)
                → (c : ≤ₛ-grade (step-extends-state r) ·ᵣ mapᵉ ε₁' ≾ᵣ mapᵉ ε₁)
                → Sim es M' r
                ----------------------------------------------------------------
                → Sim es (handle M' `with H' `in N')
                         (HANDLE-STEP {H = H} {N = N} r c)

↝-≐ˢ-handle-step {A = A} {ε₁ = ε₁} {ε₁' = ε₁'} {St = St} {St' = St'}
                {St₁ = St₁} es M' H' N' eH eN r c
                (St₂' , M₂' , es₂ , r' , h , eM₂) =
    St₂' , _ , es₂ , HANDLE-STEP r' (step-grade-≾ r') , h
  , subst (λ z → _ ≡ z)
      (sym (cast-handle (sym (toCtx-≐ˢ es₂)) {M = M₂'}))
      (handle-≡ eM₂
        (λ op ε₃ →
           trans
             (C-rename-≡
               (cong-∷-ren-≐ʳ (cong-∷-ren-≐ʳ
                 (suc-comp-ren-≐ʳ h es es₂ (≾-⊤ᵣ _) (≾-⊤ᵣ _)))) _)
             (trans
               (C-rename-cong
                 (cong-∷-ren (cong-∷-ren
                   (castʳ² (cong (_⟨ ⊤ᵣ ⟩) (sym (toCtx-≐ˢ es)))
                           (cong (_⟨ ⊤ᵣ ⟩) (sym (toCtx-≐ˢ es₂)))
                           (suc-comp-ren (step-extends-state r') (≾-⊤ᵣ _)))))
                 (eH op ε₃))
               (cast-rename-cl (sym (toCtx-≐ˢ es)) (sym (toCtx-≐ˢ es₂))
                               (suc-comp-ren (step-extends-state r')
                                             (≾-⊤ᵣ _))
                               (H' op ε₃))))
        (trans
          (C-rename-≡ (cong-∷-ren-≐ʳ (suc-comp-ren-≐ʳ h es es₂ c (step-grade-≾ r'))) _)
          (subst (λ z → _ ≡ z)
            (trans (cast-rename-∷ (cong (_⟨ mapᵉ ε₁ ⟩) (sym (toCtx-≐ˢ es)))
                                  (cong (_⟨ mapᵉ ε₁' ⟩) (sym (toCtx-≐ˢ es₂)))
                                  (suc-comp-ren (step-extends-state r')
                                                (step-grade-≾ r'))
                                  N')
                   (castᶜ-irr (cong (_∷ A) (cong (_⟨ mapᵉ ε₁' ⟩) (sym (toCtx-≐ˢ es₂))))
                              (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε₁' ⟩ ∷ A) (sym (toCtx-≐ˢ es₂)))
                              (C-rename (cong-∷-ren (suc-comp-ren
                                          (step-extends-state r')
                                          (step-grade-≾ r'))) N')))
            (C-rename-cong (cong-∷-ren _)
              (subst (λ z → _ ≡ z) (castᶜ-irr _ _ N') eN)))))

-- One clause per rule. The two congruences recurse, and hand the
-- recursion's `_≤≐_` witness on.

↝-≐ˢ : ∀ {A ε ε₁} {St St' St₁ : 𝕊 []}
    → (es : St ≐ˢ St')
    → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε}
    → M ≡ castᶜ (sym (toCtx-≐ˢ es)) M'
    → {N : toCtx St₁ ⊢C⦂ A ‼ ε₁}
    → (r : ⟨ St , M ⟩ ↝ ⟨ St₁ , N ⟩)
    -------------------------------
    → Sim es M' r

↝-≐ˢ es eM APP         = ↝-≐ˢ-app es _ eM
↝-≐ˢ es eM MATCH       = ↝-≐ˢ-match es _ eM
↝-≐ˢ es eM IF-TRUE     = ↝-≐ˢ-if-true es _ eM
↝-≐ˢ es eM IF-FALSE    = ↝-≐ˢ-if-false es _ eM
↝-≐ˢ es eM SEQ-RET     = ↝-≐ˢ-seq-ret es _ eM
↝-≐ˢ es eM SEQ-OP      = ↝-≐ˢ-seq-op es _ eM
↝-≐ˢ es eM DELAY       = ↝-≐ˢ-delay es _ eM
↝-≐ˢ es eM HANDLE-RET  = ↝-≐ˢ-handle-ret es _ eM
↝-≐ˢ es eM HANDLE-OP   = ↝-≐ˢ-handle-op es _ eM
↝-≐ˢ es eM BOX         = ↝-≐ˢ-box es _ eM
↝-≐ˢ es eM UNBOX       = ↝-≐ˢ-unbox es _ eM
↝-≐ˢ es eM SUB-APP     = ↝-≐ˢ-sub-app es _ eM
↝-≐ˢ es eM SUB-IF      = ↝-≐ˢ-sub-if es _ eM
↝-≐ˢ es eM SUB-RET     = ↝-≐ˢ-sub-ret es _ eM
↝-≐ˢ es eM SUB-OP      = ↝-≐ˢ-sub-op es _ eM

-- sequencing: simulate the head, then rebuild
↝-≐ˢ es eM (SEQ-STEP {ε₁ = ε₁} {ε₃ = ε₃} {A = A} r c)
  with cast-seq⁻ (sym (toCtx-≐ˢ es)) _ eM
... | M₁' , N' , refl , eM₁ , eN with ↝-≐ˢ es eM₁ r
...   | St₂' , M₂' , es₂ , r' , h , eM₂ =
    St₂' , _ , es₂ , SEQ-STEP r' (step-grade-≾ r') , h
  , subst (λ z → _ ≡ z)
      (sym (cast-seq (sym (toCtx-≐ˢ es₂)) {M = M₂'}
             {N = C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r')
                                                     (step-grade-≾ r'))) N'}))
    (cong₂ _⨟_ eM₂
      (trans
        (C-rename-≡ (cong-∷-ren-≐ʳ (suc-comp-ren-≐ʳ h es es₂ c (step-grade-≾ r'))) _)
        (subst (λ z → _ ≡ z)
          (trans (cast-rename-∷ (cong (_⟨ mapᵉ ε₁ ⟩) (sym (toCtx-≐ˢ es)))
                                (cong (_⟨ mapᵉ ε₃ ⟩) (sym (toCtx-≐ˢ es₂)))
                                (suc-comp-ren (step-extends-state r')
                                              (step-grade-≾ r'))
                                N')
                 (castᶜ-irr (cong (_∷ A) (cong (_⟨ mapᵉ ε₃ ⟩) (sym (toCtx-≐ˢ es₂))))
                            (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε₃ ⟩ ∷ A) (sym (toCtx-≐ˢ es₂)))
                            (C-rename (cong-∷-ren (suc-comp-ren
                                        (step-extends-state r')
                                        (step-grade-≾ r'))) N')))
          (C-rename-cong (cong-∷-ren _)
            (subst (λ z → _ ≡ z) (castᶜ-irr _ _ N') eN)))))

↝-≐ˢ es eM (HANDLE-STEP r c) with cast-handle⁻ (sym (toCtx-≐ˢ es)) _ eM
... | M₁' , H' , N' , refl , eM₁ , eH , eN =
  ↝-≐ˢ-handle-step es M₁' H' N' eH eN r c (↝-≐ˢ es eM₁ r)

↝-≐ˢ es eM (SUB-STEP {p = p} {q = q} r) with cast-sub⁻ (sym (toCtx-≐ˢ es)) _ eM
... | p₁ ‼ₛ q₁ , M₁' , refl , eM₁ =
  ↝-≐ˢ-sub-step es M₁' p q p₁ q₁ r (↝-≐ˢ es eM₁ r)

-- The bisimulation extends to runs, step by step.

↝*-≐ˢ : ∀ {A ε ε₁} {St St' St₁ : 𝕊 []}
     → (es : St ≐ˢ St')
     → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε}
     → M ≡ castᶜ (sym (toCtx-≐ˢ es)) M'
     → {N : toCtx St₁ ⊢C⦂ A ‼ ε₁}
     → ⟨ St , M ⟩ ↝* ⟨ St₁ , N ⟩
     -------------------------------------------------------------------
     → Σ[ St₁' ∈ 𝕊 [] ] Σ[ N' ∈ (toCtx St₁' ⊢C⦂ A ‼ ε₁) ]
       Σ[ es₁ ∈ St₁ ≐ˢ St₁' ]
         (⟨ St' , M' ⟩ ↝* ⟨ St₁' , N' ⟩)
       × (N ≡ castᶜ (sym (toCtx-≐ˢ es₁)) N')

↝*-≐ˢ {St' = St'} es {M' = M'} eM ε* = St' , M' , es , ε* , eM
↝*-≐ˢ es eM (r ◅ rs) with ↝-≐ˢ es eM r
... | St₂' , N₂' , es₂ , r' , _ , eN₂ with ↝*-≐ˢ es₂ eN₂ rs
...   | St₁' , N' , es₁ , rs' , eN = St₁' , N' , es₁ , r' ◅ rs' , eN

