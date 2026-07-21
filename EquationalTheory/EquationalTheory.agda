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

  data _⊢V⦂_==_ (Γ : Ctx) : {A B : VType} → Γ ⊢V⦂ A → Γ ⊢V⦂ B → Set where

    -- reflexivity, symmetry, transitivity

    V-refl : ∀ {A}
           → {V : Γ ⊢V⦂ A}
           ---------------
           → Γ ⊢V⦂ V == V

    V-sym : ∀ {A B}
          → {V : Γ ⊢V⦂ A}
          → {W : Γ ⊢V⦂ B}
          → Γ ⊢V⦂ V == W
          -----------------
          → Γ ⊢V⦂ W == V

    V-trans : ∀ {A B C}
            → {V : Γ ⊢V⦂ A}
            → {W : Γ ⊢V⦂ B}
            → {U : Γ ⊢V⦂ C}
            → Γ ⊢V⦂ V == W
            → Γ ⊢V⦂ W == U
            -------------------
            → Γ ⊢V⦂ V == U

    -- substitutivity

    V-subst : ∀ {Γ' A B B' ρ}
            → {V : Γ' ⊢V⦂ B}
            → {W : Γ' ⊢V⦂ B'}
            → (p : Γ' ⊢V⦂ V == W)
            → (x : A ∈[ ρ ] Γ')
            → (q : split-l x ++ᶜ split-r x ≡ Γ)
            → (U : split-l x ⊢V⦂ A)
            ---------------------------------------------------------------
            → Γ ⊢V⦂ subst (_⊢V⦂ B) q (V [ x ↦ U ]v)
                == subst (_⊢V⦂ B') q (W [ x ↦ U ]v)

    -- congruence equations

    ⦉⦊-cong : ∀ {A A' B B'}
           → {V : Γ ⊢V⦂ A}
           → {V' : Γ ⊢V⦂ A'}
           → {W : Γ ⊢V⦂ B}
           → {W' : Γ ⊢V⦂ B'}
           → Γ ⊢V⦂ V == V'
           → Γ ⊢V⦂ W == W'
           ------------------------------
           → Γ ⊢V⦂ ⦉ V , W ⦊ == ⦉ V' , W' ⦊

    lam-cong : ∀ {A B B' ε}
             → {M : Γ ∷ A ⊢C⦂ B ‼ ε}
             → {N : Γ ∷ A ⊢C⦂ B' ‼ ε}
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

  data _⊢C⦂_==_ (Γ : Ctx) : {C D : CType} → Γ ⊢C⦂ C → Γ ⊢C⦂ D → Set where

    -- reflexivity, symmetry, transitivity

    C-refl : ∀ {C}
           → {M : Γ ⊢C⦂ C}
           ---------------
           → Γ ⊢C⦂ M == M

    C-sym : ∀ {C D}
          → {M : Γ ⊢C⦂ C}
          → {N : Γ ⊢C⦂ D}
          → Γ ⊢C⦂ M == N
          -----------------
          → Γ ⊢C⦂ N == M

    C-trans : ∀ {C D E}
            → {M : Γ ⊢C⦂ C}
            → {N : Γ ⊢C⦂ D}
            → {P : Γ ⊢C⦂ E}
            → Γ ⊢C⦂ M == N
            → Γ ⊢C⦂ N == P
            -------------------
            → Γ ⊢C⦂ M == P

    -- substitutivity

    C-subst : ∀ {Γ' A C D ρ}
            → {M : Γ' ⊢C⦂ C}
            → {N : Γ' ⊢C⦂ D}
            → (p : Γ' ⊢C⦂ M == N)
            → (x : A ∈[ ρ ] Γ')
            → (q : split-l x ++ᶜ split-r x ≡ Γ)
            → (V : split-l x ⊢V⦂ A)
            ---------------------------------------------------------------
            → Γ ⊢C⦂ subst (_⊢C⦂ C) q (M [ x ↦ V ]c)
                == subst (_⊢C⦂ D) q (N [ x ↦ V ]c)

    -- congruence equations

    return-cong : ∀ {A B}
                → {V : Γ ⊢V⦂ A}
                → {W : Γ ⊢V⦂ B}
                → Γ ⊢V⦂ V == W
                ----------------------------
                → Γ ⊢C⦂ return V == return W

    seq-cong : ∀ {A B B' ε ε' ε''}
             → {M M' : Γ ⊢C⦂ A ‼ ε}
             → {N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
             → {N' : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε''}
             → Γ ⊢C⦂ M == M'
             → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ N == N'
             ---------------------------------
             → Γ ⊢C⦂ M ⨟ N == M' ⨟ N'

    app-cong : ∀ {A C D}
             → {V : Γ ⊢V⦂ A ⇒ C}
             → {V' : Γ ⊢V⦂ A ⇒ D}
             → {W W' : Γ ⊢V⦂ A}
             → Γ ⊢V⦂ V == V'
             → Γ ⊢V⦂ W == W'
             ------------------------
             → Γ ⊢C⦂ V · W == V' · W'

    match-cong : ∀ {A B C D}
               → {V W : Γ ⊢V⦂ A |×| B}
               → {M : Γ ∷ A ∷ B ⊢C⦂ C}
               → {N : Γ ∷ A ∷ B ⊢C⦂ D}
               → Γ ⊢V⦂ V == W
               → Γ ∷ A ∷ B ⊢C⦂ M == N
               --------------------------------------
               → Γ ⊢C⦂ match V `in M == match W `in N

    absurd-cong : ∀ {C}
                → {V W : Γ ⊢V⦂ Empty}
                → Γ ⊢V⦂ V == W
                ------------------------------------
                → Γ ⊢C⦂ absurd {C = C} V == absurd {C = C} W

    perform-cong : ∀ {A A' ε ε' op}
                 → {V W : Γ ⊢V⦂ type-of-gtype (param op)}
                 → {M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
                 → {N : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A' ‼ ε'}
                 → Γ ⊢V⦂ V == W
                 → Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ M == N
                 ---------------------------------------------------------------
                 → Γ ⊢C⦂ perform op V M == perform op W N

    delay-cong  : ∀ {A A' τ ε ε'}
                → {M : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε}
                → {N : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A' ‼ ε'}
                → Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ M == N
                --------------------------------------
                → Γ ⊢C⦂ delay τ M == delay τ N

    handle-cong : ∀ {A B ε ε'}
                → {M M' : Γ ⊢C⦂ A ‼ ε}
                → {H H' : ((op : Op) → (ε'' : E) → (Γ' : Ctx) →
                             Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                                         ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                             ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))}
                → {N N' : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
                → Γ ⊢C⦂ M == M'
                → ((op : Op) → (ε'' : E) → (Γ' : Ctx) →
                     Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                     ⊢C⦂ H op ε'' Γ' == H' op ε'' Γ')
                → Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ N == N'
                --------------------------------------------------------------------
                → Γ ⊢C⦂ handle M `with H `in N == handle M' `with H' `in N'

    unbox-cong : ∀ {A C D ρ Δ}
               → {w : Ren (Δ ⟨ ρ ⟩) Γ}
               → {V W : Δ ⊢V⦂ [ ρ ] A}
               → {M : Γ ∷ A  ⊢C⦂ C}
               → {N : Γ ∷ A  ⊢C⦂ D}
               → Δ ⊢V⦂ V == W
               → Γ ∷ A ⊢C⦂ M == N
               ------------------------------------
               → Γ ⊢C⦂ unbox w V M == unbox w W N

    box-cong : ∀ {A C D ρ}
             → {V W : Γ ⟨ ρ ⟩ ⊢V⦂ A}
             → {M : Γ ∷ [ ρ ] A ⊢C⦂ C}
             → {N : Γ ∷ [ ρ ] A ⊢C⦂ D}
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
              → (w : Ren (Δ ⟨ ρ ⟩) Γ)
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
                  → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx) →
                           Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
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
                   → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx) →
                            Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                                        ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                            ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                   → (N : Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
                   ----------------------------------------------------------------
                   → Γ ⊢C⦂ handle perform op V M `with H `in N
                       == ε-subst (sym (·ₑ-assoc (op-grade op) ε ε'))
                            (box (lam
                                   (handle M
                                   `with (λ op' ε'' Γ' →
                                            C-rename
                                              (cong-ren (ren-ᴱ-∷ {Γ = Γ ⟨ mapᵉ (op-grade op) ⟩}
                                                          (type-of-gtype (arity op))))
                                              (H op' ε'' Γ'))
                                   `in (C-rename
                                         (cong-∷-ren
                                           (cong-⟨⟩-ren wk-ren
                                            ∘ʳ ⟨⟩-μ-ren
                                            ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-·ᵉ)))
                                         N)))
                                  (C-rename (cong-∷-ren (cong-∷-ren (contract Γ)))
                                    (H op (ε ·ₑ ε') Γ)
                                   [ Tl-∷ Hd ↦ V ]c))

    handle-delay : ∀ {A B τ ε ε'}
                 → (M : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
                 → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx) →
                          Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
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
                 → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx) →
                          Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                                      ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ C ‼ ε'')
                          ⊢C⦂ C ‼ (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
                 ------------------------------------------------------------------------------
                 → Γ ⊢C⦂ handle box V M `with H `in N
                     == box V
                        (handle M `with H
                        `in (C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N))


    handle-unbox : ∀ {A B C ρ Δ ε ε'}
                 → (w : Ren (Δ ⟨ ρ ⟩) Γ)
                 → (V : Δ ⊢V⦂ [ ρ ] A)
                 → (M : Γ ∷ A ⊢C⦂ B ‼ ε)
                 → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx) →
                          Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
                                      ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ C ‼ ε'')
                          ⊢C⦂ C ‼ (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
                 -----------------------------------------------------------------
                 → Γ ⊢C⦂ handle unbox w V M `with H `in N
                     == unbox w V
                        (handle M
                        `with (λ op' ε'' Γ' →
                                 C-rename (cong-ren (ren-ᴱ-∷ {Γ = Γ} A)) (H op' ε'' Γ'))
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
               → (w₁ : Ren (Δ₁ ⟨ ρ₁ ⟩) Γ)
               → (V₁ : Δ₁ ⊢V⦂ [ ρ₁ ] A)
               → (w₂ : Ren (Δ₂ ⟨ ρ₂ ⟩) Γ)
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
                   → (w : Ren (Δ ⟨ ρ ⟩) Γ)
                   → (V : Δ ⊢V⦂ [ ρ ] A)
                   → (M : Γ ⊢C⦂ C)
                   -------------------------------------
                   → Γ ⊢C⦂ unbox w V (C-rename wk-ren M)
                       == M

    -- boxing and unboxing unrelated resources commute

    box-unbox-comm : ∀ {A B C ρ ρ₂ Δ₂}
                   → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
                   → (w₂ : Ren (Δ₂ ⟨ ρ₂ ⟩) Γ)
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
                  → (H : (op : Op) → (ε₀ : E) → (Γ' : Ctx) →
                           Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
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


-- The heterogeneously defined equational theory is no more powerful
-- than a homogeneous one: equated values have equal types, and equated
-- computations have equal types.

mutual

  ⊢V⦂==-is-homogeneous : ∀ {Γ A B} {V : Γ ⊢V⦂ A} {W : Γ ⊢V⦂ B}
                      → Γ ⊢V⦂ V == W
                      --------------
                      → A ≡ B

  ⊢V⦂==-is-homogeneous V-refl =
    refl
  ⊢V⦂==-is-homogeneous (V-sym p) =
    sym (⊢V⦂==-is-homogeneous p)
  ⊢V⦂==-is-homogeneous (V-trans p q) =
    trans (⊢V⦂==-is-homogeneous p) (⊢V⦂==-is-homogeneous q)
  ⊢V⦂==-is-homogeneous (V-subst p x q V) =
    ⊢V⦂==-is-homogeneous p
  ⊢V⦂==-is-homogeneous (⦉⦊-cong p q) =
    cong₂ _|×|_
      (⊢V⦂==-is-homogeneous p)
      (⊢V⦂==-is-homogeneous q)
  ⊢V⦂==-is-homogeneous (lam-cong {A = A} p) =
    cong (A ⇒_) (⊢C⦂==-is-homogeneous p)
  ⊢V⦂==-is-homogeneous (unit-eta _) =
    refl
  ⊢V⦂==-is-homogeneous (fun-eta _) =
    refl

  ⊢C⦂==-is-homogeneous : ∀ {Γ C D} {M : Γ ⊢C⦂ C} {N : Γ ⊢C⦂ D}
                      → Γ ⊢C⦂ M == N
                      --------------
                      → C ≡ D

  ⊢C⦂==-is-homogeneous C-refl =
    refl
  ⊢C⦂==-is-homogeneous (C-sym p) =
    sym (⊢C⦂==-is-homogeneous p)
  ⊢C⦂==-is-homogeneous (C-trans p q) =
    trans (⊢C⦂==-is-homogeneous p) (⊢C⦂==-is-homogeneous q)
  ⊢C⦂==-is-homogeneous (C-subst p x q V) =
    ⊢C⦂==-is-homogeneous p
  ⊢C⦂==-is-homogeneous (return-cong p) =
    cong (_‼ uₑ) (⊢V⦂==-is-homogeneous p)
  ⊢C⦂==-is-homogeneous (seq-cong {ε = ε} p q) =
    cong₂ (λ B ε' → B ‼ (ε ·ₑ ε'))
      (‼-injective-ty (⊢C⦂==-is-homogeneous q))
      (‼-injective-egrade (⊢C⦂==-is-homogeneous q))
  ⊢C⦂==-is-homogeneous (app-cong p q) =
    ⇒-injective-cod (⊢V⦂==-is-homogeneous p)
  ⊢C⦂==-is-homogeneous (match-cong p q) =
    ⊢C⦂==-is-homogeneous q
  ⊢C⦂==-is-homogeneous (absurd-cong p) =
    refl
  ⊢C⦂==-is-homogeneous (perform-cong {op = op} p q) =
    cong₂ (λ A ε → A ‼ (op-grade op ·ₑ ε))
      (‼-injective-ty (⊢C⦂==-is-homogeneous q))
      (‼-injective-egrade (⊢C⦂==-is-homogeneous q))
  ⊢C⦂==-is-homogeneous (delay-cong {τ = τ} p) =
    cong₂ (λ A ε' → A ‼ (of-natᵉ τ ·ₑ ε'))
      (‼-injective-ty (⊢C⦂==-is-homogeneous p))
      (‼-injective-egrade (⊢C⦂==-is-homogeneous p))
  ⊢C⦂==-is-homogeneous (handle-cong {ε = ε} p q r) =
    cong₂ (λ A ε' → A ‼ (ε ·ₑ ε'))
      (‼-injective-ty (⊢C⦂==-is-homogeneous r))
      (‼-injective-egrade (⊢C⦂==-is-homogeneous r))
  ⊢C⦂==-is-homogeneous (unbox-cong vp p) =
    ⊢C⦂==-is-homogeneous p
  ⊢C⦂==-is-homogeneous (box-cong p q) =
    ⊢C⦂==-is-homogeneous q
  ⊢C⦂==-is-homogeneous (coerce-cong p) =
    refl
  ⊢C⦂==-is-homogeneous (seq-return V M) =
    refl
  ⊢C⦂==-is-homogeneous (seq-perform V M N) =
    refl
  ⊢C⦂==-is-homogeneous (seq-delay M N) =
    refl
  ⊢C⦂==-is-homogeneous (seq-box V M N) =
    refl
  ⊢C⦂==-is-homogeneous (seq-unbox w V M N) =
    refl
  ⊢C⦂==-is-homogeneous (seq-eta _) =
    refl
  ⊢C⦂==-is-homogeneous (seq-assoc M N P) =
    refl
  ⊢C⦂==-is-homogeneous (fun-beta M W) =
    refl
  ⊢C⦂==-is-homogeneous (match-beta V W M) =
    refl
  ⊢C⦂==-is-homogeneous (match-eta V M) =
    refl
  ⊢C⦂==-is-homogeneous (absurd-eta V M) =
    refl
  ⊢C⦂==-is-homogeneous (handle-return V H N) =
    refl
  ⊢C⦂==-is-homogeneous (handle-perform V M H N) =
    refl
  ⊢C⦂==-is-homogeneous (handle-delay M H N) =
    refl
  ⊢C⦂==-is-homogeneous (handle-box V M H N) =
    refl
  ⊢C⦂==-is-homogeneous (handle-unbox w V M H N) =
    refl
  ⊢C⦂==-is-homogeneous (unbox-beta V K p N) =
    refl
  ⊢C⦂==-is-homogeneous (unbox-comm w₁ V₁ w₂ V₂ M) =
    refl
  ⊢C⦂==-is-homogeneous (box-comm V W M) =
    refl
  ⊢C⦂==-is-homogeneous (boxed-not-used V M) =
    refl
  ⊢C⦂==-is-homogeneous (unbox-not-used w V _) =
    refl
  ⊢C⦂==-is-homogeneous (box-unbox-comm V w₂ V₂ M) =
    refl
  ⊢C⦂==-is-homogeneous (coerce-refl rel M) =
    refl
  ⊢C⦂==-is-homogeneous (coerce-trans rel rel' rel'' M) =
    refl
  ⊢C⦂==-is-homogeneous (coerce-perform rel V M) =
    refl
  ⊢C⦂==-is-homogeneous (coerce-delay rel M) =
    refl
  ⊢C⦂==-is-homogeneous (coerce-seq rel M N) =
    refl
  ⊢C⦂==-is-homogeneous (coerce-handle rel M H N) =
    refl
  ⊢C⦂==-is-homogeneous (delay-zero M) =
    refl
  ⊢C⦂==-is-homogeneous (delay-delay M) =
    refl
