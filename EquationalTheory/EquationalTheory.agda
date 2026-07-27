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

    V-subst : ∀ {Γ' A B ρ}
            → {V W : Γ' ⊢V⦂ B}
            → (p : Γ' ⊢V⦂ V == W)
            → (x : A ∈[ ρ ] Γ')
            → (q : split-l x ++ᶜ split-r x ≡ Γ)
            → (U : split-l x ⊢V⦂ A)
            ---------------------------------------------------------------
            → Γ ⊢V⦂ subst (_⊢V⦂ B) q (V [ x ↦ U ]v)
                == subst (_⊢V⦂ B) q (W [ x ↦ U ]v)

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

    C-subst : ∀ {Γ' A C ρ}
            → {M N : Γ' ⊢C⦂ C}
            → (p : Γ' ⊢C⦂ M == N)
            → (x : A ∈[ ρ ] Γ')
            → (q : split-l x ++ᶜ split-r x ≡ Γ)
            → (V : split-l x ⊢V⦂ A)
            ---------------------------------------------------------------
            → Γ ⊢C⦂ subst (_⊢C⦂ C) q (M [ x ↦ V ]c)
                == subst (_⊢C⦂ C) q (N [ x ↦ V ]c)

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
                             Γ ᴱ ∷ type-of-gtype (param op)
                                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                             ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))}
                → {N N' : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
                → Γ ⊢C⦂ M == M'
                → ((op : Op) → (ε'' : E) →
                     Γ ᴱ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                     ⊢C⦂ H op ε'' == H' op ε'')
                → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ N == N'
                --------------------------------------------------------------------
                → Γ ⊢C⦂ handle M `with H `in N == handle M' `with H' `in N'

    unbox-cong : ∀ {A C ρ Δ}
               → {w : Ren [] (Δ ⟨ ρ ⟩) Γ}
               → {V W : Δ ⊢V⦂ [ ρ ] A}
               → {M N : Γ ∷ A  ⊢C⦂ C}
               → Δ ⊢V⦂ V == W
               → Γ ∷ A ⊢C⦂ M == N
               ------------------------------------
               → Γ ⊢C⦂ unbox w V M == unbox w W N

    box-cong : ∀ {A C ρ}
             → {V W : Γ ⟨ ρ ⟩ ⊢V⦂ A}
             → {M N : Γ ∷ [ ρ ] A ⊢C⦂ C}
             → Γ ⟨ ρ ⟩ ⊢V⦂ V == W
             → Γ ∷ [ ρ ] A ⊢C⦂ M == N
             --------------------------
             → Γ ⊢C⦂ box V M == box W N

    coerce-cong : ∀ {A ε ε'}
                → {rel rel' : ε ≾ₑ ε'}
                → {M N : Γ ⊢C⦂ A ‼ ε}
                → Γ ⊢C⦂ M == N
                -----------------------------------
                → Γ ⊢C⦂ coerce rel M == coerce rel' N

    -- computational/beta-equations for sequential composition

    seq-return : ∀ {A B ε}
               → (V : Γ ⊢V⦂ A)
               → (M : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
               -----------------------------------------------------
               → Γ ⊢C⦂ return V ⨟ M
                   == ε-subst (sym (·ₑ-identityˡ ε))
                        ((C-rename
                           (cong-∷-ren
                             (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-uᵉ)))
                           M)
                         [ Hd ↦ V ]c)

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
                                 (cong-⟨⟩-ren wk-ren
                                  ∘ʳ ⟨⟩-μ-ren
                                  ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)))
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
                              (⟨⟩-μ-ren
                               ∘ʳ eq-ren (cong (Γ ⟨_⟩)
                                               (trans map-·ᵉ
                                                      (cong (_·ᵣ mapᵉ ε) map-of-natᵉ)))))
                            N))

    seq-box : ∀ {A B C ρ ε ε'}
            → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
            → (M : Γ ∷ [ ρ ] A ⊢C⦂ B ‼ ε)
            → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
            -------------------------------------------------------
            → Γ ⊢C⦂ box V M ⨟ N
                == box V (M ⨟ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N)

    seq-unbox : ∀ {A B C ρ Δ ε ε'}
              → (w : Ren [] (Δ ⟨ ρ ⟩) Γ)
              → (V : Δ ⊢V⦂ [ ρ ] A)
              → (M : Γ ∷ A ⊢C⦂ B ‼ ε)
              → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
              -------------------------------------------------------
              → Γ ⊢C⦂ unbox w V M ⨟ N
                  == unbox w V (M ⨟ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N)

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
                                     (cong-⟨⟩-ren wk-ren
                                      ∘ʳ ⟨⟩-μ-ren
                                      ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)))
                                   P))

    -- computational/beta-equation for function application

    fun-beta : ∀ {A C}
             → (M : Γ ∷ A ⊢C⦂ C)
             → (W : Γ ⊢V⦂ A)
             ----------------------
             → Γ ⊢C⦂ lam M · W
                 == M [ Hd ↦ W ]c

    -- beta-equation for pattern-matching

    match-beta : ∀ {A B C}
               → (V : Γ ⊢V⦂ A)
               → (W : Γ ⊢V⦂ B)
               → (M : Γ ∷ A ∷ B ⊢C⦂ C)
               ------------------------------------
               → Γ ⊢C⦂ match ⦉ V , W ⦊ `in M
                   == M [ Hd ↦ V-rename wk-ren W ]c
                        [ Hd ↦ V ]c

    -- eta-equation for pattern-matching

    match-eta : ∀ {A B C}
              → (V : Γ ⊢V⦂ A |×| B)
              → (M : Γ ∷ A |×| B ⊢C⦂ C)
              -------------------------------------------------------------
              → Γ ⊢C⦂ match V `in
                       ((C-rename (exch-ren ∘ʳ wk-ren ∘ʳ exch-ren ∘ʳ wk-ren)
                         M) [ Hd ↦ ⦉ var (λ _ → ≾ᵣ-refl) (Tl-∷ Hd) , var (λ _ → ≾ᵣ-refl) Hd ⦊ ]c)
                  == M [ Hd ↦ V ]c

    -- eta-equation for empty type elimination

    absurd-eta : ∀ {C}
               → (V : Γ ⊢V⦂ Empty)
               → (M : Γ ∷ Empty ⊢C⦂ C)
               -----------------------
               → Γ ⊢C⦂ absurd {C = C} V
                   == M [ Hd ↦ V ]c

    -- computational/beta-equations for effect handling

    handle-return : ∀ {A B ε}
                  → (V : Γ ⊢V⦂ A)
                  → (H : (op : Op) → (ε'' : E) →
                           Γ ᴱ ∷ type-of-gtype (param op)
                               ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                           ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                  → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
                  ----------------------------------------------------------------
                  → Γ ⊢C⦂ handle return V `with H `in N
                      == ε-subst (sym (·ₑ-identityˡ ε))
                           ((C-rename
                              (cong-∷-ren
                                (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-uᵉ)))
                              N)
                            [ Hd ↦ V ]c)

    handle-perform : ∀ {A B ε ε' op}
                   → (V : Γ ⊢V⦂ type-of-gtype (param op))
                   → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
                   → (H : (op : Op) → (ε'' : E) →
                            Γ ᴱ ∷ type-of-gtype (param op)
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
                                                (ren-ᴱ-∷ {Γ ⟨ mapᵉ (op-grade op) ⟩}
                                                         (type-of-gtype (arity op)))))
                                              (H op' ε''))
                                   `in (C-rename
                                         (cong-∷-ren
                                           (cong-⟨⟩-ren wk-ren
                                            ∘ʳ ⟨⟩-μ-ren
                                            ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)))
                                         N)))
                                  (C-rename (cong-∷-ren (cong-∷-ren (ᴱ-ren Γ)))
                                    (H op (ε ·ₑ ε'))
                                   [ Tl-∷ Hd ↦ V ]c))

    handle-delay : ∀ {A B τ ε ε'}
                 → (M : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
                 → (H : (op : Op) → (ε'' : E) →
                          Γ ᴱ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                          ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ mapᵉ (of-natᵉ τ ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
                 ------------------------------------------------------------------------------
                 → Γ ⊢C⦂ handle delay τ M `with H `in N
                     == ε-subst (sym (·ₑ-assoc (of-natᵉ τ) ε ε'))
                          (delay τ
                            (handle M
                            `with H
                            `in (C-rename
                                  (cong-∷-ren
                                    (⟨⟩-μ-ren
                                     ∘ʳ eq-ren (cong (Γ ⟨_⟩)
                                                     (trans map-·ᵉ
                                                            (cong (_·ᵣ mapᵉ ε) map-of-natᵉ)))))
                                  N)))

    handle-box : ∀ {A B C ρ ε ε'}
                 → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
                 → (M : Γ ∷ [ ρ ] A ⊢C⦂ B ‼ ε)
                 → (H : (op : Op) → (ε'' : E) →
                          Γ ᴱ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ C ‼ ε'')
                          ⊢C⦂ C ‼ (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
                 ------------------------------------------------------------------------------
                 → Γ ⊢C⦂ handle box V M `with H `in N
                     == box V
                        (handle M `with H
                        `in (C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N))


    handle-unbox : ∀ {A B C ρ Δ ε ε'}
                 → (w : Ren [] (Δ ⟨ ρ ⟩) Γ)
                 → (V : Δ ⊢V⦂ [ ρ ] A)
                 → (M : Γ ∷ A ⊢C⦂ B ‼ ε)
                 → (H : (op : Op) → (ε'' : E) →
                          Γ ᴱ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ C ‼ ε'')
                          ⊢C⦂ C ‼ (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
                 -----------------------------------------------------------------
                 → Γ ⊢C⦂ handle unbox w V M `with H `in N
                     == unbox w V
                        (handle M
                        `with (λ op' ε'' →
                                 C-rename (cong-∷-ren (cong-∷-ren (ren-ᴱ-∷ {Γ} A)))
                                   (H op' ε''))
                        `in (C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N))

    -- beta rule for unbox

    unbox-beta : ∀ {A C D ρ}
               → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
               → (K : Γ ∷ [ ρ ] A ⊢K[ all ◁ D ]⦂ C)
               → (p : ctx-grade (hole-ctx K) ≾ᵣ ρ)
               → (N : (Γ ∷ [ ρ ] A ++ᶜ hole-ctx K) ∷ A ⊢C⦂ D)
               -----------------------------------------------------------------------
               → Γ ⊢C⦂ box V (K [ unbox (wk-ren-⟨ρ⟩-ctx refl ∘ʳ ⟨⟩-≤-ren p)
                                        (var (λ _ → ≾ᵣ-refl) Hd)
                                        N ])
                   == box V (K [ N [ Hd ↦ V-rename (wk-ren-⟨ρ⟩-ctx refl ∘ʳ ⟨⟩-≤-ren p ∘ʳ cong-⟨⟩-ren wk-ren) V ]c ])


    -- unboxing non-related values commute

    unbox-comm : ∀ {A B C ρ₁ Δ₁ ρ₂ Δ₂}
               → (w₁ : Ren [] (Δ₁ ⟨ ρ₁ ⟩) Γ)
               → (V₁ : Δ₁ ⊢V⦂ [ ρ₁ ] A)
               → (w₂ : Ren [] (Δ₂ ⟨ ρ₂ ⟩) Γ)
               → (V₂ : Δ₂ ⊢V⦂ [ ρ₂ ] B)
               → (M : Γ ∷ A ∷ B ⊢C⦂ C)
               ----------------------------------------------------
               → Γ ⊢C⦂ unbox w₁ V₁
                        (unbox (wk-ren ∘ʳ w₂) V₂ M)
                   == unbox w₂ V₂
                        (unbox (wk-ren ∘ʳ w₁) V₁
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

    unbox-not-used : ∀ {A C ρ Δ}
                   → (w : Ren [] (Δ ⟨ ρ ⟩) Γ)
                   → (V : Δ ⊢V⦂ [ ρ ] A)
                   → (M : Γ ⊢C⦂ C)
                   -------------------------------------
                   → Γ ⊢C⦂ unbox w V (C-rename wk-ren M)
                       == M

    -- boxing and unboxing unrelated resources commute

    box-unbox-comm : ∀ {A B C ρ ρ₂ Δ₂}
                   → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
                   → (w₂ : Ren [] (Δ₂ ⟨ ρ₂ ⟩) Γ)
                   → (V₂ : Δ₂ ⊢V⦂ [ ρ₂ ] B)
                   → (M : Γ ∷ [ ρ ] A ∷ B ⊢C⦂ C)
                   -----------------------------------
                   → Γ ⊢C⦂ box V
                            (unbox (wk-ren ∘ʳ w₂) V₂ M)
                       == unbox w₂ V₂
                            (box
                              (V-rename (cong-⟨⟩-ren wk-ren) V)
                              (C-rename exch-ren M))

    -- equations for sub-effecting coercions
    --
    -- Coercion is a coercion, not structure: it is functorial in the effect
    -- witness (`coerce-refl`/`coerce-trans`, no dependence on which witness is
    -- used — that is already `coerce-cong`), and it commutes with the two
    -- effect-grade formers, so a coercion of the continuation is unobservable
    -- from outside the operation or delay. These are the syntactic image of the
    -- monad's `T-≤-refl`, `T-≤-trans`, `opᵀ-≤` and `delayᵀ-≤`.

    coerce-refl : ∀ {A ε}
                → (rel : ε ≾ₑ ε)
                → (M : Γ ⊢C⦂ A ‼ ε)
                ---------------------------
                → Γ ⊢C⦂ coerce rel M == M

    coerce-trans : ∀ {A ε₁ ε₂ ε₃}
                 → (rel : ε₁ ≾ₑ ε₂) → (rel' : ε₂ ≾ₑ ε₃) → (rel'' : ε₁ ≾ₑ ε₃)
                 → (M : Γ ⊢C⦂ A ‼ ε₁)
                 ------------------------------------------------------
                 → Γ ⊢C⦂ coerce rel' (coerce rel M) == coerce rel'' M

    coerce-perform : ∀ {A ε ε' op}
                   → (rel : ε ≾ₑ ε')
                   → (V : Γ ⊢V⦂ type-of-gtype (param op))
                   → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                          ⊢C⦂ A ‼ ε)
                   ----------------------------------------------------------
                   → Γ ⊢C⦂ coerce (·ₑ-monoʳ-≾ₑ rel) (perform op V M)
                        == perform op V (coerce rel M)

    coerce-delay : ∀ {A τ ε ε'}
                 → (rel : ε ≾ₑ ε')
                 → (M : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
                 ------------------------------------------------
                 → Γ ⊢C⦂ coerce (·ₑ-monoʳ-≾ₑ rel) (delay τ M)
                      == delay τ (coerce rel M)

    -- Coercing the *handled*/sequenced computation is coercing the composite.
    -- The continuation lives under the lock `Γ ⟨ mapᵉ ε ⟩`, which the coercion
    -- relaxes, so it is reindexed along `⟨⟩-≤-ren` (the box being contravariant
    -- in its grade — the model's `strᵀ-≤`).

    coerce-seq : ∀ {A B ε₁ ε₂ ε'}
               → (rel : ε₁ ≾ₑ ε₂)
               → (M : Γ ⊢C⦂ A ‼ ε₁)
               → (N : Γ ⟨ mapᵉ ε₂ ⟩ ∷ A ⊢C⦂ B ‼ ε')
               ------------------------------------------------------------
               → Γ ⊢C⦂ (coerce rel M) ⨟ N
                    == coerce (·ₑ-monoˡ-≾ₑ rel)
                         (M ⨟ C-rename (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N)

    coerce-handle : ∀ {A B ε₁ ε₂ ε'}
                  → (rel : ε₁ ≾ₑ ε₂)
                  → (M : Γ ⊢C⦂ A ‼ ε₁)
                  → (H : (op : Op) → (ε₀ : E) →
                           Γ ᴱ ∷ type-of-gtype (param op)
                               ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₀)
                           ⊢C⦂ B ‼ (op-grade op ·ₑ ε₀))
                  → (N : Γ ⟨ mapᵉ ε₂ ⟩ ∷ A ⊢C⦂ B ‼ ε')
                  ----------------------------------------------------------------
                  → Γ ⊢C⦂ handle (coerce rel M) `with H `in N
                       == coerce (·ₑ-monoˡ-≾ₑ rel)
                            (handle M `with H
                               `in (C-rename (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N))

    -- equations for collapsing successive delays

    delay-zero : ∀ {A ε}
               → (M : Γ ⟨ of-natʳ 0 ⟩ ⊢C⦂ A ‼ ε)
               --------------------------
               → Γ ⊢C⦂ delay 0 M
                   == ε-subst (sym (trans (cong (_·ₑ ε) of-natᵉ-zero) (·ₑ-identityˡ ε)))
                        (C-rename
                          (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) of-natʳ-zero))
                          M)

    delay-delay : ∀ {A τ₁ τ₂ ε}
                → (M : Γ ⟨ of-natʳ (τ₁ + τ₂) ⟩ ⊢C⦂ A ‼ ε)
                ------------------------------------
                → Γ ⊢C⦂ delay τ₁ (delay τ₂
                           (C-rename
                             (⟨⟩-μ-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) of-natʳ-plus))
                             M))
                    == ε-subst (trans (cong (_·ₑ ε) of-natᵉ-plus) (·ₑ-assoc (of-natᵉ τ₁) (of-natᵉ τ₂) ε))
                         (delay (τ₁ + τ₂) M)

  infix 18 _⊢C⦂_==_
