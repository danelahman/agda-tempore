---------------------------------------
-- Equational theory of the language --
---------------------------------------

open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module EquationalTheory.EquationalTheory (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.CompContext   S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.RenActions    S
open import Syntax.Renamings     S
open import Syntax.Substitutions S
open import Syntax.Types         S

open import Syntax.Renamings.Equivalence S using (∈-++ᶜˡ; grade-++ᶜˡ-uᵣ)

-- Binder narrowing, shared with the two sequencing rules of the operational
-- semantics.

open import OperationalSemantics.PreservationTheorem S using (narrow-∷)


-- Equations between well-typed values and computations

mutual

  -- value equations

  data _⊢V⦂_==_ (Γ : Ctx) : {A : VType} → Γ ⊢V⦂ A → Γ ⊢V⦂ A → Set where

    -- reflexivity, symmetry, transitivity

    V-refl : ∀ {A}
           → {V : Γ ⊢V⦂ A}
           ---------------
           → Γ ⊢V⦂ V == V

    V-sym : ∀ {A}
          → {V W : Γ ⊢V⦂ A}
          → Γ ⊢V⦂ V == W
          -----------------
          → Γ ⊢V⦂ W == V

    V-trans : ∀ {A}
            → {V W U : Γ ⊢V⦂ A}
            → Γ ⊢V⦂ V == W
            → Γ ⊢V⦂ W == U
            -------------------
            → Γ ⊢V⦂ V == U

    -- substitutivity

    V-subst : ∀ {Γ' Γ₁ Γ₂ A B}
            → {V W : Γ' ⊢V⦂ B}
            → (p : Γ' ⊢V⦂ V == W)
            → (s : Γ₁ ∷ A , Γ₂ split Γ')
            → (q : Γ₁ ++ᶜ Γ₂ ≡ Γ)
            → (U : Γ₁ ⊢V⦂ A)
            ---------------------------------------------------------------
            → Γ ⊢V⦂ subst (_⊢V⦂ B) q (V [ s ↦ U ]v)
                == subst (_⊢V⦂ B) q (W [ s ↦ U ]v)

    -- congruence equations

    ⦉⦊-cong : ∀ {A B}
           → {V V' : Γ ⊢V⦂ A}
           → {W W' : Γ ⊢V⦂ B}
           → Γ ⊢V⦂ V == V'
           → Γ ⊢V⦂ W == W'
           ------------------------------
           → Γ ⊢V⦂ ⦉ V , W ⦊ == ⦉ V' , W' ⦊

    lam-cong : ∀ {A B ε}
             → {M N : Γ ∷ A ⊢C⦂ B ‼ ε}
             → Γ ∷ A ⊢C⦂ M == N
             -------------------------
             → Γ ⊢V⦂ lam M == lam N

    -- eta equations

    unit-eta : (V : Γ ⊢V⦂ Unit)
             ------------------
             → Γ ⊢V⦂ V == ⋆

    fun-eta : ∀ {A C}
            → (V : Γ ⊢V⦂ A ⇒ C)
            -----------------------------------------------
            → Γ ⊢V⦂ V
                == lam (V-rename wk-ren V · var (λ _ → ≾ᵣ-refl) Hd)

    -- equations for subsumption
    --
    -- Subsumption is erased, so it obeys exactly the laws of the coercion it
    -- denotes: witness irrelevance, and functoriality in the witness.

    subV-cong : ∀ {A A'}
              → {w w' : A <:ᵛ A'}
              → {V W : Γ ⊢V⦂ A}
              → Γ ⊢V⦂ V == W
              ------------------------------
              → Γ ⊢V⦂ subV V w == subV W w'

    subV-refl : ∀ {A}
              → (w : A <:ᵛ A)
              → (V : Γ ⊢V⦂ A)
              ----------------------
              → Γ ⊢V⦂ subV V w == V

    subV-trans : ∀ {A₁ A₂ A₃}
               → (w : A₁ <:ᵛ A₂) → (w' : A₂ <:ᵛ A₃) → (w'' : A₁ <:ᵛ A₃)
               → (V : Γ ⊢V⦂ A₁)
               ------------------------------------------
               → Γ ⊢V⦂ subV (subV V w) w' == subV V w''

  infix 18 _⊢V⦂_==_

  -- computation equations

  data _⊢C⦂_==_ (Γ : Ctx) : {C : CType} → Γ ⊢C⦂ C → Γ ⊢C⦂ C → Set where

    -- reflexivity, symmetry, transitivity

    C-refl : ∀ {C}
           → {M : Γ ⊢C⦂ C}
           ---------------
           → Γ ⊢C⦂ M == M

    C-sym : ∀ {C}
          → {M N : Γ ⊢C⦂ C}
          → Γ ⊢C⦂ M == N
          -----------------
          → Γ ⊢C⦂ N == M

    C-trans : ∀ {C}
            → {M N P : Γ ⊢C⦂ C}
            → Γ ⊢C⦂ M == N
            → Γ ⊢C⦂ N == P
            -------------------
            → Γ ⊢C⦂ M == P

    -- substitutivity

    C-subst : ∀ {Γ' Γ₁ Γ₂ A C}
            → {M N : Γ' ⊢C⦂ C}
            → (p : Γ' ⊢C⦂ M == N)
            → (s : Γ₁ ∷ A , Γ₂ split Γ')
            → (q : Γ₁ ++ᶜ Γ₂ ≡ Γ)
            → (V : Γ₁ ⊢V⦂ A)
            ---------------------------------------------------------------
            → Γ ⊢C⦂ subst (_⊢C⦂ C) q (M [ s ↦ V ]c)
                == subst (_⊢C⦂ C) q (N [ s ↦ V ]c)

    -- congruence equations

    return-cong : ∀ {A}
                → {V W : Γ ⊢V⦂ A}
                → Γ ⊢V⦂ V == W
                ----------------------------
                → Γ ⊢C⦂ return V == return W

    seq-cong : ∀ {A B ε ε'}
             → {M M' : Γ ⊢C⦂ A ‼ ε}
             → {N N' : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
             → Γ ⊢C⦂ M == M'
             → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ N == N'
             ---------------------------------
             → Γ ⊢C⦂ M ⨟ N == M' ⨟ N'

    app-cong : ∀ {A C}
             → {V V' : Γ ⊢V⦂ A ⇒ C}
             → {W W' : Γ ⊢V⦂ A}
             → Γ ⊢V⦂ V == V'
             → Γ ⊢V⦂ W == W'
             ------------------------
             → Γ ⊢C⦂ V · W == V' · W'

    match-cong : ∀ {A B C}
               → {V W : Γ ⊢V⦂ A |×| B}
               → {M N : Γ ∷ A ∷ B ⊢C⦂ C}
               → Γ ⊢V⦂ V == W
               → Γ ∷ A ∷ B ⊢C⦂ M == N
               --------------------------------------
               → Γ ⊢C⦂ match V `in M == match W `in N

    absurd-cong : ∀ {C}
                → {V W : Γ ⊢V⦂ Empty}
                → Γ ⊢V⦂ V == W
                ------------------------------------
                → Γ ⊢C⦂ absurd {C = C} V == absurd {C = C} W

    if-cong : ∀ {C}
            → {V W : Γ ⊢V⦂ Bool}
            → {M M' N N' : Γ ⊢C⦂ C}
            → Γ ⊢V⦂ V == W
            → Γ ⊢C⦂ M == M'
            → Γ ⊢C⦂ N == N'
            ----------------------------------------------------------
            → Γ ⊢C⦂ if V `then M `else N == if W `then M' `else N'

    perform-cong : ∀ {A ε op}
                 → {V W : Γ ⊢V⦂ type-of-gtype (param op)}
                 → {M N : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
                 → Γ ⊢V⦂ V == W
                 → Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ M == N
                 ---------------------------------------------------------------
                 → Γ ⊢C⦂ perform op V M == perform op W N

    delay-cong  : ∀ {A τ ε}
                → {M N : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε}
                → Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ M == N
                --------------------------------------
                → Γ ⊢C⦂ delay τ M == delay τ N

    handle-cong : ∀ {A B ε ε'}
                → {M M' : Γ ⊢C⦂ A ‼ ε}
                → {H H' : ((op : Op) → (ε'' : E) →
                             Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                             ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))}
                → {N N' : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
                → Γ ⊢C⦂ M == M'
                → ((op : Op) → (ε'' : E) →
                     Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                     ⊢C⦂ H op ε'' == H' op ε'')
                → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ N == N'
                --------------------------------------------------------------------
                → Γ ⊢C⦂ handle M `with H `in N == handle M' `with H' `in N'

    -- The grade bound and the payload subsumption an `unbox` stores are both
    -- irrelevant, so the two nodes are compared at the resource variable they
    -- name.

    unbox-cong : ∀ {A A₀ C ρ₀ ρ'}
               → {x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ}
               → {rel rel' : ρ' ≾ᵣ ρ₀}
               → {w w' : A₀ <:ᵛ A}
               → {M N : Γ ∷ A  ⊢C⦂ C}
               → Γ ∷ A ⊢C⦂ M == N
               ------------------------------------------------
               → Γ ⊢C⦂ unbox x rel w M == unbox x rel' w' N

    box-cong : ∀ {A C ρ}
             → {V W : Γ ⟨ ρ ⟩ ⊢V⦂ A}
             → {M N : Γ ∷ [ ρ ] A ⊢C⦂ C}
             → Γ ⟨ ρ ⟩ ⊢V⦂ V == W
             → Γ ∷ [ ρ ] A ⊢C⦂ M == N
             --------------------------
             → Γ ⊢C⦂ box V M == box W N

    subC-cong : ∀ {C C'}
              → {w w' : C <:ᶜ C'}
              → {M N : Γ ⊢C⦂ C}
              → Γ ⊢C⦂ M == N
              ------------------------------
              → Γ ⊢C⦂ subC M w == subC N w'

    -- computational/beta-equations for sequential composition

    seq-return : ∀ {A B ε}
               → (V : Γ ⊢V⦂ A)
               → (M : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
               -----------------------------------------------------
               → Γ ⊢C⦂ return V ⨟ M
                   == ε-subst (sym (·ₑ-identityˡ ε))
                        ((C-rename
                           (cong-∷-ren
                             (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren))
                           M)
                         [ split-[] ↦ V ]c)

    seq-perform : ∀ {A B ε ε' op}
                → (V : Γ ⊢V⦂ type-of-gtype (param op))
                → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
                → (N : Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
                ---------------------------------------------------------------------
                → Γ ⊢C⦂ (perform op V M) ⨟ N
                    == ε-subst (sym (·ₑ-assoc (op-grade op) ε ε'))
                         (perform op V
                            (M ⨟
                             C-rename
                               (cong-∷-ren
                                 ((eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)
                                  ∘ʳ ⟨⟩-μ-ren)
                                  ∘ʳ cong-⟨⟩-ren wk-ren))
                               N))

    seq-delay : ∀ {A B τ ε ε'}
              → (M : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
              → (N : Γ ⟨ mapᵉ (of-natᵉ τ ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
              -------------------------------------------------------
              → Γ ⊢C⦂ delay τ M ⨟ N
                  == ε-subst (sym (·ₑ-assoc (of-natᵉ τ) ε ε'))
                       (delay τ
                         (M ⨟
                          C-rename
                            (cong-∷-ren
                              (eq-ren (cong (Γ ⟨_⟩)
                                               (trans map-·ᵉ
                                                      (cong (_·ᵣ mapᵉ ε) map-of-natᵉ)))
                               ∘ʳ ⟨⟩-μ-ren))
                            N))

    seq-box : ∀ {A B C ρ ε ε'}
            → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
            → (M : Γ ∷ [ ρ ] A ⊢C⦂ B ‼ ε)
            → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
            -------------------------------------------------------
            → Γ ⊢C⦂ box V M ⨟ N
                == box V (M ⨟ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N)

    seq-unbox : ∀ {A A₀ B C ρ₀ ρ' ε ε'}
              → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
              → (rel : ρ' ≾ᵣ ρ₀)
              → (w : A₀ <:ᵛ A)
              → (M : Γ ∷ A ⊢C⦂ B ‼ ε)
              → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
              -------------------------------------------------------
              → Γ ⊢C⦂ unbox x rel w M ⨟ N
                  == unbox x rel w (M ⨟ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N)

    -- eta-equation for sequential composition

    seq-eta : ∀ {A ε}
            → (M : Γ ⊢C⦂ A ‼ ε)
            ----------------------------------------------------------
            → Γ ⊢C⦂ M
                == ε-subst (·ₑ-identityʳ ε) (M ⨟ return (var (λ _ → ≾ᵣ-refl) Hd))

    -- associativity equation for sequential composition

    seq-assoc : ∀ {A B C ε ε' ε''}
              → (M : Γ ⊢C⦂ A ‼ ε)
              → (N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
              → (P : Γ ⟨ mapᵉ (ε ·ₑ ε') ⟩ ∷ B ⊢C⦂ C ‼ ε'')
              ---------------------------------------------------------------------
              → Γ ⊢C⦂ (M ⨟ N) ⨟ P
                  == ε-subst (sym (·ₑ-assoc ε ε' ε''))
                       (M ⨟ (N ⨟ C-rename
                                   (cong-∷-ren
                                     ((eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)
                                      ∘ʳ ⟨⟩-μ-ren)
                                      ∘ʳ cong-⟨⟩-ren wk-ren))
                                   P))

    -- computational/beta-equation for function application

    fun-beta : ∀ {A C}
             → (M : Γ ∷ A ⊢C⦂ C)
             → (W : Γ ⊢V⦂ A)
             ----------------------
             → Γ ⊢C⦂ lam M · W
                 == M [ split-[] ↦ W ]c

    -- beta-equation for pattern-matching

    match-beta : ∀ {A B C}
               → (V : Γ ⊢V⦂ A)
               → (W : Γ ⊢V⦂ B)
               → (M : Γ ∷ A ∷ B ⊢C⦂ C)
               ------------------------------------
               → Γ ⊢C⦂ match ⦉ V , W ⦊ `in M
                   == M [ split-[] ↦ V-rename wk-ren W ]c
                        [ split-[] ↦ V ]c

    -- eta-equation for pattern-matching

    match-eta : ∀ {A B C}
              → (V : Γ ⊢V⦂ A |×| B)
              → (M : Γ ∷ A |×| B ⊢C⦂ C)
              -------------------------------------------------------------
              → Γ ⊢C⦂ match V `in
                       ((C-rename (wk-ren ∘ʳ exch-ren ∘ʳ wk-ren ∘ʳ exch-ren)
                         M) [ split-[] ↦ ⦉ var (λ _ → ≾ᵣ-refl) (Tl-∷ Hd) , var (λ _ → ≾ᵣ-refl) Hd ⦊ ]c)
                  == M [ split-[] ↦ V ]c

    -- eta-equation for empty type elimination

    absurd-eta : ∀ {C}
               → (V : Γ ⊢V⦂ Empty)
               → (M : Γ ∷ Empty ⊢C⦂ C)
               -----------------------
               → Γ ⊢C⦂ absurd {C = C} V
                   == M [ split-[] ↦ V ]c

    -- beta-equations for boolean elimination

    if-beta-true : ∀ {C}
                 → (M N : Γ ⊢C⦂ C)
                 -----------------------------------------
                 → Γ ⊢C⦂ if true `then M `else N == M

    if-beta-false : ∀ {C}
                  → (M N : Γ ⊢C⦂ C)
                  -----------------------------------------
                  → Γ ⊢C⦂ if false `then M `else N == N

    -- eta-equation for boolean elimination
    --
    -- Commuting conversions are instances of this rule.

    if-eta : ∀ {C}
           → (V : Γ ⊢V⦂ Bool)
           → (M : Γ ∷ Bool ⊢C⦂ C)
           ------------------------------------------------------
           → Γ ⊢C⦂ if V `then (M [ split-[] ↦ true  ]c)
                        `else (M [ split-[] ↦ false ]c)
               == M [ split-[] ↦ V ]c

    -- computational/beta-equations for effect handling
    --
    -- Each equation re-bars the clause family across the binder or lock the handle moves under.

    handle-return : ∀ {A B ε}
                  → (V : Γ ⊢V⦂ A)
                  → (H : (op : Op) → (ε'' : E) →
                           Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                               ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                           ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                  → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
                  ----------------------------------------------------------------
                  → Γ ⊢C⦂ handle return V `with H `in N
                      == ε-subst (sym (·ₑ-identityˡ ε))
                           ((C-rename
                              (cong-∷-ren
                                (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren))
                              N)
                            [ split-[] ↦ V ]c)

    handle-perform : ∀ {A B ε ε' op}
                   → (V : Γ ⊢V⦂ type-of-gtype (param op))
                   → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
                   → (H : (op : Op) → (ε'' : E) →
                            Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                                ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                            ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                   → (N : Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
                   ----------------------------------------------------------------
                   → Γ ⊢C⦂ handle perform op V M `with H `in N
                       == ε-subst (sym (·ₑ-assoc (op-grade op) ε ε'))
                            (box (lam
                                   (handle M
                                   `with (λ op' ε'' →
                                            C-rename
                                              (cong-∷-ren (cong-∷-ren
                                                (barrier-wk-ren {Γ} (mapᵉ (op-grade op))
                                                                (type-of-gtype (arity op)))))
                                              (H op' ε''))
                                   `in (C-rename
                                         (cong-∷-ren
                                           ((eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)
                                            ∘ʳ ⟨⟩-μ-ren)
                                            ∘ʳ cong-⟨⟩-ren wk-ren))
                                         N)))
                                  (C-rename (cong-∷-ren (cong-∷-ren barrier-ren))
                                    (H op (ε ·ₑ ε'))
                                   [ split-∷ split-[] ↦ V ]c))

    handle-delay : ∀ {A B τ ε ε'}
                 → (M : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
                 → (H : (op : Op) → (ε'' : E) →
                          Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                          ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ mapᵉ (of-natᵉ τ ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
                 ------------------------------------------------------------------------------
                 → Γ ⊢C⦂ handle delay τ M `with H `in N
                     == ε-subst (sym (·ₑ-assoc (of-natᵉ τ) ε ε'))
                          (delay τ
                            (handle M
                            `with (λ op' ε'' →
                                     C-rename (cong-∷-ren (cong-∷-ren
                                       (⟨⟩-≤-ren (≾-⊤ᵣ _) ∘ʳ ⟨⟩-μ-ren)))
                                       (H op' ε''))
                            `in (C-rename
                                  (cong-∷-ren
                                    (eq-ren (cong (Γ ⟨_⟩)
                                                     (trans map-·ᵉ
                                                            (cong (_·ᵣ mapᵉ ε) map-of-natᵉ)))
                                     ∘ʳ ⟨⟩-μ-ren))
                                  N)))

    handle-box : ∀ {A B C ρ ε ε'}
                 → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
                 → (M : Γ ∷ [ ρ ] A ⊢C⦂ B ‼ ε)
                 → (H : (op : Op) → (ε'' : E) →
                          Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ C ‼ ε'')
                          ⊢C⦂ C ‼ (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
                 ------------------------------------------------------------------------------
                 → Γ ⊢C⦂ handle box V M `with H `in N
                     == box V
                        (handle M
                        `with (λ op' ε'' →
                                 C-rename (cong-∷-ren (cong-∷-ren
                                   (cong-⟨⟩-ren (wk-ren {Δ = Γ} {A = [ ρ ] A}))))
                                   (H op' ε''))
                        `in (C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N))


    handle-unbox : ∀ {A A₀ B C ρ₀ ρ' ε ε'}
                 → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
                 → (rel : ρ' ≾ᵣ ρ₀)
                 → (w : A₀ <:ᵛ A)
                 → (M : Γ ∷ A ⊢C⦂ B ‼ ε)
                 → (H : (op : Op) → (ε'' : E) →
                          Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ C ‼ ε'')
                          ⊢C⦂ C ‼ (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
                 -----------------------------------------------------------------
                 → Γ ⊢C⦂ handle unbox x rel w M `with H `in N
                     == unbox x rel w
                        (handle M
                        `with (λ op' ε'' →
                                 C-rename (cong-∷-ren (cong-∷-ren
                                   (cong-⟨⟩-ren (wk-ren {Δ = Γ} {A = A}))))
                                   (H op' ε''))
                        `in (C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N))

    -- beta rule for unbox

    unbox-beta : ∀ {A A' C D ρ}
               → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
               → (K : Γ ∷ [ ρ ] A ⊢K[ all ◁ D ]⦂ C)
               → (p : ctx-grade (hole-ctx K) ≾ᵣ ρ)
               → (w : A <:ᵛ A')
               → (N : (Γ ∷ [ ρ ] A ++ᶜ hole-ctx K) ∷ A' ⊢C⦂ D)
               -----------------------------------------------------------------------
               → Γ ⊢C⦂ box V (K [ unbox (∈-++ᶜˡ (hole-ctx K) Hd)
                                        (≾ᵣ-trans (≾ᵣ-reflexive
                                                    (grade-++ᶜˡ-uᵣ (hole-ctx K)))
                                                  p)
                                        w N ])
                   == box V (K [ N [ split-[] ↦ subV (V-rename ((cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-≤-ren p) ∘ʳ wk-ren-⟨ρ⟩-ctx refl) V) w ]c ])


    -- unboxing non-related values commute

    unbox-comm : ∀ {A A₁ B B₂ C ρ₁ ρ₁' ρ₂ ρ₂'}
               → (x₁ : [ ρ₁ ] A₁ ∈[ ρ₁' ] Γ)
               → (rel₁ : ρ₁' ≾ᵣ ρ₁)
               → (w₁ : A₁ <:ᵛ A)
               → (x₂ : [ ρ₂ ] B₂ ∈[ ρ₂' ] Γ)
               → (rel₂ : ρ₂' ≾ᵣ ρ₂)
               → (w₂ : B₂ <:ᵛ B)
               → (M : Γ ∷ A ∷ B ⊢C⦂ C)
               ----------------------------------------------------
               → Γ ⊢C⦂ unbox x₁ rel₁ w₁
                        (unbox (Tl-∷ x₂) rel₂ w₂ M)
                   == unbox x₂ rel₂ w₂
                        (unbox (Tl-∷ x₁) rel₁ w₁
                               (C-rename exch-ren M))


    -- boxing resources commute

    box-comm : ∀ {A B C ρ ρ'}
             → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
             → (W : Γ ⟨ ρ' ⟩ ⊢V⦂ B)
             → (M : Γ ∷ [ ρ ] A ∷ [ ρ' ] B ⊢C⦂ C)
             -------------------------------------------------
             → Γ ⊢C⦂ box V
                     (box (V-rename (cong-⟨⟩-ren wk-ren) W) M)
                 == box W
                     (box
                       (V-rename (cong-⟨⟩-ren wk-ren) V)
                       (C-rename exch-ren M))

    -- eta rule for box
    
    boxed-not-used : ∀ {A C ρ ε}
                   → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
                   → (M : Γ ⊢C⦂ C ‼ ε)
                   -----------------------------------
                   → Γ ⊢C⦂ box V (C-rename wk-ren M)
                       == M

    -- eta rule for unbox

    unbox-not-used : ∀ {A A₀ C ρ₀ ρ'}
                   → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
                   → (rel : ρ' ≾ᵣ ρ₀)
                   → (w : A₀ <:ᵛ A)
                   → (M : Γ ⊢C⦂ C)
                   ---------------------------------------------------
                   → Γ ⊢C⦂ unbox x rel w (C-rename (wk-ren {A = A}) M)
                       == M

    -- boxing and unboxing unrelated resources commute

    box-unbox-comm : ∀ {A B B₂ C ρ ρ₂ ρ₂'}
                   → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
                   → (x₂ : [ ρ₂ ] B₂ ∈[ ρ₂' ] Γ)
                   → (rel₂ : ρ₂' ≾ᵣ ρ₂)
                   → (w₂ : B₂ <:ᵛ B)
                   → (M : Γ ∷ [ ρ ] A ∷ B ⊢C⦂ C)
                   -----------------------------------
                   → Γ ⊢C⦂ box V
                            (unbox (Tl-∷ x₂) rel₂ w₂ M)
                       == unbox x₂ rel₂ w₂
                            (box
                              (V-rename (cong-⟨⟩-ren wk-ren) V)
                              (C-rename exch-ren M))

    -- equations for subsumption
    --
    -- Subsumption is functorial in the witness and commutes with the
    -- operation/delay effect formers. Sub-effecting is the special case at an
    -- effect-only witness, so `coerce` needs no equations of its own.

    subC-refl : ∀ {C}
              → (w : C <:ᶜ C)
              → (M : Γ ⊢C⦂ C)
              ------------------------
              → Γ ⊢C⦂ subC M w == M

    subC-trans : ∀ {C₁ C₂ C₃}
               → (w : C₁ <:ᶜ C₂) → (w' : C₂ <:ᶜ C₃) → (w'' : C₁ <:ᶜ C₃)
               → (M : Γ ⊢C⦂ C₁)
               ----------------------------------------------
               → Γ ⊢C⦂ subC (subC M w) w' == subC M w''

    subC-perform : ∀ {A A' ε ε' op}
                 → (w : A <:ᵛ A')
                 → (rel : ε ≾ₑ ε')
                 → (V : Γ ⊢V⦂ type-of-gtype (param op))
                 → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                        ⊢C⦂ A ‼ ε)
                 ----------------------------------------------------------
                 → Γ ⊢C⦂ subC (perform op V M) (w ‼ₛ ·ₑ-monoʳ-≾ₑ rel)
                      == perform op V (subC M (w ‼ₛ rel))

    subC-delay : ∀ {A A' τ ε ε'}
               → (w : A <:ᵛ A')
               → (rel : ε ≾ₑ ε')
               → (M : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
               ------------------------------------------------
               → Γ ⊢C⦂ subC (delay τ M) (w ‼ₛ ·ₑ-monoʳ-≾ₑ rel)
                    == delay τ (subC M (w ‼ₛ rel))

    -- Moving a scrutinee's subsumption outwards relaxes the continuation's
    -- lock along the effect half and narrows its binder along the value half.
    -- Neither `_⨟_` nor `handle_`with_`in` carries a payload witness of its
    -- own, as `unbox` does.

    subC-seq : ∀ {A A' B ε₁ ε₂ ε'}
             → (w : A <:ᵛ A')
             → (rel : ε₁ ≾ₑ ε₂)
             → (M : Γ ⊢C⦂ A ‼ ε₁)
             → (N : Γ ⟨ mapᵉ ε₂ ⟩ ∷ A' ⊢C⦂ B ‼ ε')
             ------------------------------------------------------------
             → Γ ⊢C⦂ subC M (w ‼ₛ rel) ⨟ N
                  == coerce (·ₑ-monoˡ-≾ₑ rel)
                       (M ⨟ narrow-∷ w
                              (C-rename
                                (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N))

    subC-handle : ∀ {A A' B ε₁ ε₂ ε'}
                → (w : A <:ᵛ A')
                → (rel : ε₁ ≾ₑ ε₂)
                → (M : Γ ⊢C⦂ A ‼ ε₁)
                → (H : (op : Op) → (ε₀ : E) →
                         Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₀)
                         ⊢C⦂ B ‼ (op-grade op ·ₑ ε₀))
                → (N : Γ ⟨ mapᵉ ε₂ ⟩ ∷ A' ⊢C⦂ B ‼ ε')
                ----------------------------------------------------------------
                → Γ ⊢C⦂ handle (subC M (w ‼ₛ rel)) `with H `in N
                     == coerce (·ₑ-monoˡ-≾ₑ rel)
                          (handle M `with H
                             `in (narrow-∷ w
                                    (C-rename
                                      (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N)))

    -- equations for collapsing successive delays

    delay-zero : ∀ {A ε}
               → (M : Γ ⟨ of-natʳ 0 ⟩ ⊢C⦂ A ‼ ε)
               --------------------------
               → Γ ⊢C⦂ delay 0 M
                   == ε-subst (sym (trans (cong (_·ₑ ε) of-natᵉ-zero) (·ₑ-identityˡ ε)))
                        (C-rename
                          (eq-ren (cong (Γ ⟨_⟩) of-natʳ-zero) ∘ʳ ⟨⟩-η-ren)
                          M)

    delay-delay : ∀ {A τ₁ τ₂ ε}
                → (M : Γ ⟨ of-natʳ (τ₁ + τ₂) ⟩ ⊢C⦂ A ‼ ε)
                ------------------------------------
                → Γ ⊢C⦂ delay τ₁ (delay τ₂
                           (C-rename
                             (eq-ren (cong (Γ ⟨_⟩) of-natʳ-plus) ∘ʳ ⟨⟩-μ-ren)
                             M))
                    == ε-subst (trans (cong (_·ₑ ε) of-natᵉ-plus) (·ₑ-assoc (of-natᵉ τ₁) (of-natᵉ τ₂) ε))
                         (delay (τ₁ + τ₂) M)

  infix 18 _⊢C⦂_==_
