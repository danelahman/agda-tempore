------------------------------------------------------------------------
-- Overview of the monomorphic calculus
--
-- One entry per main definition, rule, lemma and theorem, under its
-- title: the calculus, its operational semantics and type safety, the
-- equational theory, the denotational semantics and adequacy. The items
-- not yet formalised are listed at the end. Check it with
-- `agda MonomorphicCalculus/Results.agda`.
--
-- The calculus is parameterised by a `LanguageSpec` (a grade system, base
-- types and an operation signature).
------------------------------------------------------------------------

module MonomorphicCalculus.Results where

open import Language.Spec public using (LanguageSpec)


------------------------------------------------------------------------
-- The monomorphic calculus

module TheMonomorphicCalculus (S : LanguageSpec) where

  -- Types, contexts, eternal types, the grade of a context, and
  -- variables under locks
  open import MonomorphicCalculus.Syntax.Types S public
    using (GType; VType; CType; Eternal; type-of-gtype)
    renaming ( Unitₑ to Et-Unit ; Boolₑ to Et-Bool ; Natₑ to Et-Nat ; Emptyₑ to Et-Empty
             ; Baseₑ to Et-Base
             ; _|×|ₑ_ to Et-Prod ; _|+|ₑ_ to Et-Sum ; |List|ₑ to Et-List )
  open import MonomorphicCalculus.Syntax.Contexts S public
    using (Ctx; ctx-grade; _∈[_]_; Hd; Tl-∷; Tl-⟨⟩)

  -- Subtyping
  open import MonomorphicCalculus.Syntax.Subtyping S public
    using (_<:ᵛ_; _<:ᶜ_)
    renaming ( Unitₛ to S-Unit ; Boolₛ to S-Bool ; Natₛ to S-Nat ; Emptyₛ to S-Empty
             ; Baseₛ to S-Base
             ; _|×|ₛ_ to S-Prod ; _|+|ₛ_ to S-Sum ; |List|ₛ to S-List
             ; _⇒ₛ_ to S-Fun ; [_]ₛ_ to S-Box ; _‼ₛ_ to S-Comp )

  -- Typing of values and of computations
  open import MonomorphicCalculus.Syntax.Terms S public
    using (_⊢V⦂_; _⊢C⦂_)
    renaming ( var to Var ; ⋆ to Unit ; true to True ; false to False ; zero to Zero
             ; succ to Succ ; ⦉_,_⦊ to Pair ; inl to Inl ; inr to Inr ; nil to Nil
             ; cons to Cons ; lam to Fun ; subV to Sub-V ; const to Const-Base
             ; return to Return ; _⨟_ to Let ; _·_ to App ; match_`in_ to Match
             ; absurd to Absurd ; cmp to Cmp ; if_`then_`else_ to If
             ; caseℕ_`zero_`succ_ to Case-Nat ; recℕ to Rec-Nat
             ; case+_`inl_`inr_ to Case-Sum ; caseL_`nil_`cons_ to Case-List
             ; recL to Rec-List ; perform to Perform ; delay to Delay
             ; handle_`with_`in to Handle ; box to Box ; unbox to Unbox ; subC to Sub-C )

  -- Lemma (Subtyping): a preorder, antisymmetric where the grade orders
  -- are, reflecting eternality
  open import MonomorphicCalculus.Syntax.Subtyping S public
    using (<:ᵛ-refl; <:ᵛ-trans; <:ᵛ-antisym; <:ᵛ-irrelevant; <:ᵛ-eternalˡ)

  -- Definition (Renamings)
  open import MonomorphicCalculus.Syntax.Renaming.Base S public
    using ( Ren ; EternalCtx ; id-ren ; _∘ʳ_ ; wk-ren ; var-ren ; ⟨⟩-η-ren ; ⟨⟩-η⁻¹-ren
          ; ⟨⟩-μ-ren ; ⟨⟩-≤-ren ; ⟨⟩-ext-ctx ; cong-∷-ren ; cong-⟨⟩-ren ; exch-ren )

  -- Theorem (Renaming); Corollary (Structural rules) is its instances at
  -- the generators. Lemma (Values under locks), part 3 (Unbox-Val).
  open import MonomorphicCalculus.Syntax.Renaming.Action S public
    using (V-rename; C-rename; unbox-val)

  -- Lemma (Values under locks), parts 1 and 2
  open import MonomorphicCalculus.Syntax.Terms S public
    using (eternal-val-ext; grad-typ⇒var<:)

  -- Theorem (Substitution)
  open import MonomorphicCalculus.Syntax.Substitution S public using (_[_↦_]v; _[_↦_]c)

  -- Lemma (Context subsumption)
  open import MonomorphicCalculus.Syntax.Substitution.Subsumption S public using (subCtx)

  -- Lemma (Subsumption at reconciliation points)
  open import MonomorphicCalculus.Syntax.Normalisation S public
    using (V-normal-form; C-normal-form)


------------------------------------------------------------------------
-- Operational semantics and type safety of the monomorphic calculus

module OperationalSemanticsAndTypeSafety (S : LanguageSpec) where

  -- Definition (States)
  open import MonomorphicCalculus.OperationalSemantics.State S public
    using (𝕊; ∅; _⟨_⟩ₛ; _∷ₛ_; toCtx; state-grade; _≤ₛ_; ≤ₛ-grade; state-grade-≤ₛ)

  -- Definition (Configurations), and the small-step operational semantics.
  -- CMP reduces a comparison to its boolean; SUB, SUB-APP, SUB-IF,
  -- SUB-CASEℕ and SUB-RECℕ move a subsumption and erase to the identity on
  -- raw terms.
  open import MonomorphicCalculus.OperationalSemantics.Reduction S public
    using ( Config ; _↝_
          ; APP ; MATCH ; CMP ; IF-TRUE ; IF-FALSE ; CASEℕ-ZERO ; CASEℕ-SUCC
          ; RECℕ-ZERO ; RECℕ-SUCC ; CASE+ ; CASE-INL ; CASE-INR ; CASEL ; CASEL-NIL
          ; CASEL-CONS ; RECL ; RECL-NIL ; RECL-CONS ; SEQ-RET ; SEQ-OP ; DELAY
          ; HANDLE-RET ; HANDLE-OP ; BOX ; UNBOX ; SEQ-STEP ; HANDLE-STEP
          ; SUB ; SUB-APP ; SUB-IF ; SUB-CASEℕ ; SUB-RECℕ )

  -- Theorem (Preservation)
  open import MonomorphicCalculus.OperationalSemantics.Reduction S public
    using (step-extends-state; step-refines-type; step-grade-≾; step-invariants)

  -- Theorem (Progress)
  open import MonomorphicCalculus.OperationalSemantics.Progress S public
    using (Progresses; progress; finality-value; finality-op)

  -- Theorem (Termination)
  open import MonomorphicCalculus.OperationalSemantics.Evaluation S public using (Halts)
  open import MonomorphicCalculus.OperationalSemantics.Termination S public using (halts)

  -- Definition (Top-level semantics); Theorem (Top-level preservation and
  -- progress)
  open import MonomorphicCalculus.OperationalSemantics.TopLevel S public
    using (TopLevelOpSemantics)
  open import MonomorphicCalculus.OperationalSemantics.TopLevel.Reduction S public
    using (module PureTopLevelPreservationTheorem)
  open import MonomorphicCalculus.OperationalSemantics.TopLevel.Progress S public
    using (module PureTopLevelProgressTheorem)


------------------------------------------------------------------------
-- Equational theory and denotational semantics
--
-- The entries over a model take the model's components (`Cat`, `Fut`,
-- `Pst`, `Adj`, `GTy`, `Mon`, `GE`) as their first arguments.

module EquationalTheoryAndDenotationalSemantics (S : LanguageSpec) where

  -- Definition (Equational theory), and its axioms
  open import MonomorphicCalculus.EquationalTheory.EquationalTheory S public
    using ( _⊢V⦂_==_ ; _⊢C⦂_==_
          ; seq-return ; seq-perform ; seq-delay ; seq-box ; seq-unbox ; seq-eta
          ; seq-assoc ; fun-beta ; fun-eta ; unit-eta ; handle-return ; handle-perform
          ; handle-delay ; handle-box ; handle-unbox ; delay-zero ; delay-delay
          ; unbox-beta ; boxed-not-used ; unbox-not-used ; box-comm ; unbox-comm
          ; box-unbox-comm )

  -- Definition (Models)
  open import MonomorphicCalculus.DenotationalSemantics.Model.Category public using (Category)
  open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future public
    using (Future)
  open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past public using (Past)
  open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction public
    using (Adjunction)
  open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal public
    using (Eternalᵒ)
  open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes S public
    using (GroundTypes)
  open import MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal public
    using (GroundEternal)
  open import MonomorphicCalculus.DenotationalSemantics.Model.Monad public using (Monad)

  -- Definition (Interpretation), for derivations whose handlers are uniform
  -- (`Paramᶜ`)
  open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types public
    using (⟦_⟧ᵛ; ⟦_⟧ᶜ)
  open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts public
    using (⟦_⟧ᶜᵗˣ)
  open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms public
    using (⟦_⟧ᵛᵗ; ⟦_⟧ᶜᵗ; Paramᵛ; Paramᶜ)

  -- Theorem (Coherence with renaming and substitution)
  open import MonomorphicCalculus.DenotationalSemantics.Interpretation.RenamingCoherence public
    using (V-rename-nat; C-rename-nat)
  open import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Core public
    using (V-subst-nat; C-subst-nat)

  -- Theorem (Soundness of the equational theory)
  open import MonomorphicCalculus.EquationalTheory.Soundness public using (soundᵛ; soundᶜ)

  -- Theorem (Soundness of the operational semantics)
  open import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation public
    using (↝*-⊳)

  -- Definition (Kripke frames and the presheaf model)
  open import MonomorphicCalculus.DenotationalSemantics.Model.World public using (World)
  open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base public
    using (PShCat)
  open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Instance public
    using (PShMonad)

  -- Theorem (Adequacy), for head-faithful models; the presheaf model is
  -- one (`PShHeadFaithful` in `MonomorphicCalculus.Adequacy.PSh.HeadFaithful`);
  -- the observational corollary is `MonomorphicCalculus.Adequacy.Equational`.
  open import MonomorphicCalculus.Adequacy.HeadFaithful public using (HeadFaithful)
  open import MonomorphicCalculus.Adequacy.Adequacy public using (adequacy)
  import MonomorphicCalculus.Adequacy.PSh.HeadFaithful
  import MonomorphicCalculus.Adequacy.Equational


------------------------------------------------------------------------
-- Not yet formalised
--
--   Handler types, handler values and `handle M with V` in the
--   monomorphic calculus, its semantics and equational theory, where
--   handlers occur in `handle M with H to x in N`.
------------------------------------------------------------------------
