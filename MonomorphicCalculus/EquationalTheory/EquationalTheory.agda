---------------------------------------
-- Equational theory of the language --
---------------------------------------

open import Data.Product

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.EquationalTheory.EquationalTheory (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Language.Comparisons using (Cmp; holds)
open import MonomorphicCalculus.Syntax.CompContext   S
open import MonomorphicCalculus.Syntax.Data          S using (⟪_⟫; compareᵈ; ⌈_⌉; ⌈_⌉ᵇ)
open import MonomorphicCalculus.Syntax.Contexts      S
open import MonomorphicCalculus.Syntax.Terms      S
open import MonomorphicCalculus.Syntax.Renaming.Action S
open import MonomorphicCalculus.Syntax.Renaming      S
open import MonomorphicCalculus.Syntax.Substitution  S
open import MonomorphicCalculus.Syntax.Types S

open import MonomorphicCalculus.Syntax.Renaming.Equivalence  S using (∈-++ᶜˡ; grade-++ᶜˡ-uᵣ)

-- Binder subsumption, shared with the two sequencing rules of the operational
-- semantics.

open import MonomorphicCalculus.Syntax.Substitution.Subsumption  S using (subCtx)


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

    succ-cong : {V V' : Γ ⊢V⦂ Nat}
              → Γ ⊢V⦂ V == V'
              ---------------------------
              → Γ ⊢V⦂ succ V == succ V'

    inl-cong : ∀ {A B}
             → {V V' : Γ ⊢V⦂ A}
             → Γ ⊢V⦂ V == V'
             --------------------------------------
             → Γ ⊢V⦂ inl {B = B} V == inl {B = B} V'

    inr-cong : ∀ {A B}
             → {V V' : Γ ⊢V⦂ B}
             → Γ ⊢V⦂ V == V'
             --------------------------------------
             → Γ ⊢V⦂ inr {A = A} V == inr {A = A} V'

    cons-cong : ∀ {A}
              → {V V' : Γ ⊢V⦂ A}
              → {W W' : Γ ⊢V⦂ |List| A}
              → Γ ⊢V⦂ V == V'
              → Γ ⊢V⦂ W == W'
              ---------------------------------
              → Γ ⊢V⦂ cons V W == cons V' W'

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

    -- Subsumption is natural in the value formers: the witness splits the way
    -- its type does. At `⦉_,_⦊` that is functoriality of `_|×|_`, at `inl` and
    -- `inr` functoriality of `_|+|_`, at `nil` and `cons` functoriality of
    -- `|List|`, at `lam` functoriality of `_⇒_` —
    -- contravariant in the domain, so the binder is subsumed rather than the
    -- body coerced there. The atomic formers and `var` have no rule of their
    -- own.

    subV-pair : ∀ {A A' B B'}
              → (p : A <:ᵛ A') → (q : B <:ᵛ B')
              → (V : Γ ⊢V⦂ A)
              → (W : Γ ⊢V⦂ B)
              ------------------------------------------------------
              → Γ ⊢V⦂ subV ⦉ V , W ⦊ (p |×|ₛ q)
                   == ⦉ subV V p , subV W q ⦊

    subV-inl : ∀ {A A' B B'}
             → (p : A <:ᵛ A') → (q : B <:ᵛ B')
             → (V : Γ ⊢V⦂ A)
             ---------------------------------------------------
             → Γ ⊢V⦂ subV (inl V) (p |+|ₛ q) == inl (subV V p)

    subV-inr : ∀ {A A' B B'}
             → (p : A <:ᵛ A') → (q : B <:ᵛ B')
             → (V : Γ ⊢V⦂ B)
             ---------------------------------------------------
             → Γ ⊢V⦂ subV (inr V) (p |+|ₛ q) == inr (subV V q)

    subV-nil : ∀ {A A'}
             → (p : A <:ᵛ A')
             ---------------------------------------------
             → Γ ⊢V⦂ subV (nil {A = A}) (|List|ₛ p) == nil

    subV-cons : ∀ {A A'}
              → (p : A <:ᵛ A')
              → (V : Γ ⊢V⦂ A)
              → (W : Γ ⊢V⦂ |List| A)
              ------------------------------------------------------------
              → Γ ⊢V⦂ subV (cons V W) (|List|ₛ p)
                   == cons (subV V p) (subV W (|List|ₛ p))

    subV-lam : ∀ {A A' C C'}
             → (p : A' <:ᵛ A)
             → (w : C <:ᶜ C')
             → (M : Γ ∷ A ⊢C⦂ C)
             ------------------------------------------------------
             → Γ ⊢V⦂ subV (lam M) (p ⇒ₛ w)
                  == lam (subC (subCtx p M) w)

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

    cmp-cong : ∀ {A ⋈}
             → {V V' W W' : Γ ⊢V⦂ A}
             → {et : Eternal A}
             → Γ ⊢V⦂ V == V'
             → Γ ⊢V⦂ W == W'
             ------------------------------------------
             → Γ ⊢C⦂ cmp ⋈ V W et == cmp ⋈ V' W' et

    if-cong : ∀ {C}
            → {V W : Γ ⊢V⦂ Bool}
            → {M M' N N' : Γ ⊢C⦂ C}
            → Γ ⊢V⦂ V == W
            → Γ ⊢C⦂ M == M'
            → Γ ⊢C⦂ N == N'
            ----------------------------------------------------------
            → Γ ⊢C⦂ if V `then M `else N == if W `then M' `else N'

    caseℕ-cong : ∀ {C}
               → {V W : Γ ⊢V⦂ Nat}
               → {M M' : Γ ⊢C⦂ C}
               → {N N' : Γ ∷ Nat ⊢C⦂ C}
               → Γ ⊢V⦂ V == W
               → Γ ⊢C⦂ M == M'
               → Γ ∷ Nat ⊢C⦂ N == N'
               --------------------------------------------------------------
               → Γ ⊢C⦂ caseℕ V `zero M `succ N == caseℕ W `zero M' `succ N'

    recℕ-cong : ∀ {B ε}
              → {V W : Γ ⊢V⦂ Nat}
              → {M M' : Γ ⊢C⦂ B ‼ ε}
              → {N N' : (Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε}
              → {p : ε ·ₑ ε ≾ₑ ε}
              → Γ ⊢V⦂ V == W
              → Γ ⊢C⦂ M == M'
              → (Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ N == N'
              -----------------------------------------------
              → Γ ⊢C⦂ recℕ V M N p == recℕ W M' N' p

    caseL-cong : ∀ {A C}
               → {V W : Γ ⊢V⦂ |List| A}
               → {M M' : Γ ⊢C⦂ C}
               → {N N' : Γ ∷ A ∷ |List| A ⊢C⦂ C}
               → Γ ⊢V⦂ V == W
               → Γ ⊢C⦂ M == M'
               → Γ ∷ A ∷ |List| A ⊢C⦂ N == N'
               ------------------------------------------------------------
               → Γ ⊢C⦂ caseL V `nil M `cons N == caseL W `nil M' `cons N'

    recL-cong : ∀ {A B ε}
              → {V W : Γ ⊢V⦂ |List| A}
              → {M M' : Γ ⊢C⦂ B ‼ ε}
              → {N N' : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε}
              → {p : ε ·ₑ ε ≾ₑ ε}
              → Γ ⊢V⦂ V == W
              → Γ ⊢C⦂ M == M'
              → (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ N == N'
              ---------------------------------------------------------
              → Γ ⊢C⦂ recL V M N p == recL W M' N' p

    case+-cong : ∀ {A B C}
               → {V W : Γ ⊢V⦂ A |+| B}
               → {M M' : Γ ∷ A ⊢C⦂ C}
               → {N N' : Γ ∷ B ⊢C⦂ C}
               → Γ ⊢V⦂ V == W
               → Γ ∷ A ⊢C⦂ M == M'
               → Γ ∷ B ⊢C⦂ N == N'
               ------------------------------------------------------------
               → Γ ⊢C⦂ case+ V `inl M `inr N == case+ W `inl M' `inr N'

    perform-cong : ∀ {A ε op}
                 → {V W : Γ ⊢V⦂ type-of-gtype (param op)}
                 → {M N : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
                 → Γ ⊢V⦂ V == W
                 → Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ M == N
                 ---------------------------------------------------------------
                 → Γ ⊢C⦂ perform op V M == perform op W N

    delay-cong  : ∀ {A τ ε}
                → {M N : Γ ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε}
                → Γ ⟨ of-durʳ τ ⟩ ⊢C⦂ M == N
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
             → Γ ⊢C⦂ box _ V M == box _ W N

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
                   == ε-≃ (≃ₑ-sym (·ₑ-identityˡ ε))
                        ((C-rename
                           (cong-∷-ren
                             (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren))
                           M)
                         [ split-[] ↦ V ]c)

    seq-perform : ∀ {A B ε ε' op}
                → (V : Γ ⊢V⦂ type-of-gtype (param op))
                → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
                → (N : Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
                ---------------------------------------------------------------------
                → Γ ⊢C⦂ (perform op V M) ⨟ N
                    == ε-≃ (≃ₑ-sym (·ₑ-assoc (op-grade op) ε ε'))
                         (perform op V
                            (M ⨟
                             C-rename
                               (cong-∷-ren
                                 ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ)
                                  ∘ʳ ⟨⟩-μ-ren)
                                  ∘ʳ cong-⟨⟩-ren wk-ren))
                               N))

    seq-delay : ∀ {A B τ ε ε'}
              → (M : Γ ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε)
              → (N : Γ ⟨ mapᵉ (of-durᵉ τ ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
              -------------------------------------------------------
              → Γ ⊢C⦂ delay τ M ⨟ N
                  == ε-≃ (≃ₑ-sym (·ₑ-assoc (of-durᵉ τ) ε ε'))
                       (delay τ
                         (M ⨟
                          C-rename
                            (cong-∷-ren
                              (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ (≃ᵣ-trans map-·ᵉ (·ᵣ-cong map-of-durᵉ ≃ᵣ-refl)))
                               ∘ʳ ⟨⟩-μ-ren))
                            N))

    seq-box : ∀ {A B C ρ ε ε'}
            → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
            → (M : Γ ∷ [ ρ ] A ⊢C⦂ B ‼ ε)
            → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
            -------------------------------------------------------
            → Γ ⊢C⦂ box _ V M ⨟ N
                == box _ V (M ⨟ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N)

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
                == ε-≃ (·ₑ-identityʳ ε) (M ⨟ return (var (λ _ → ≾ᵣ-refl) Hd))

    -- associativity equation for sequential composition

    seq-assoc : ∀ {A B C ε ε' ε''}
              → (M : Γ ⊢C⦂ A ‼ ε)
              → (N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
              → (P : Γ ⟨ mapᵉ (ε ·ₑ ε') ⟩ ∷ B ⊢C⦂ C ‼ ε'')
              ---------------------------------------------------------------------
              → Γ ⊢C⦂ (M ⨟ N) ⨟ P
                  == ε-≃ (≃ₑ-sym (·ₑ-assoc ε ε' ε''))
                       (M ⨟ (N ⨟ C-rename
                                   (cong-∷-ren
                                     ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ)
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

    -- beta-equation for comparison: at data, the relation's truth on their
    -- order

    cmp-beta : ∀ {A}
             → (⋈ : Cmp)
             → (et : Eternal A)
             → (d e : ⟪ A ⟫)
             ---------------------------------------------------------------
             → Γ ⊢C⦂ cmp ⋈ (⌈ et ⌉ d) (⌈ et ⌉ e) et
                 == return ⌈ holds ⋈ (compareᵈ et d e) ⌉ᵇ

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

    -- beta-equations for natural-number elimination

    caseℕ-beta-zero : ∀ {C}
                    → (M : Γ ⊢C⦂ C)
                    → (N : Γ ∷ Nat ⊢C⦂ C)
                    -------------------------------------------
                    → Γ ⊢C⦂ caseℕ zero `zero M `succ N == M

    caseℕ-beta-succ : ∀ {C}
                    → (V : Γ ⊢V⦂ Nat)
                    → (M : Γ ⊢C⦂ C)
                    → (N : Γ ∷ Nat ⊢C⦂ C)
                    -------------------------------------------------------------
                    → Γ ⊢C⦂ caseℕ succ V `zero M `succ N == N [ split-[] ↦ V ]c

    -- eta-equation for natural-number elimination
    --
    -- Commuting conversions are instances of this rule.

    caseℕ-eta : ∀ {C}
              → (V : Γ ⊢V⦂ Nat)
              → (M : Γ ∷ Nat ⊢C⦂ C)
              ------------------------------------------------------------------
              → Γ ⊢C⦂ caseℕ V
                        `zero (M [ split-[] ↦ zero ]c)
                        `succ (C-rename (cong-∷-ren wk-ren) M
                                [ split-[] ↦ succ (var (λ _ → ≾ᵣ-refl) Hd) ]c)
                  == M [ split-[] ↦ V ]c

    -- beta-equations for primitive recursion
    --
    -- There is no eta-equation: the recursor's uniqueness is an induction
    -- principle over the scrutinee, not an equation between two terms.

    recℕ-beta-zero : ∀ {B ε}
                   → (M : Γ ⊢C⦂ B ‼ ε)
                   → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
                   → (p : ε ·ₑ ε ≾ₑ ε)
                   ---------------------------------------
                   → Γ ⊢C⦂ recℕ zero M N p == M

    recℕ-beta-succ : ∀ {B ε}
                   → (V : Γ ⊢V⦂ Nat)
                   → (M : Γ ⊢C⦂ B ‼ ε)
                   → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
                   → (p : ε ·ₑ ε ≾ₑ ε)
                   ------------------------------------------------------------
                   → Γ ⊢C⦂ recℕ (succ V) M N p
                       == coerce p (recℕ V M N p ⨟ recℕ-step V N)

    -- beta-equations for sum elimination

    case+-beta-inl : ∀ {A B C}
                   → (V : Γ ⊢V⦂ A)
                   → (M : Γ ∷ A ⊢C⦂ C)
                   → (N : Γ ∷ B ⊢C⦂ C)
                   ----------------------------------------------------------
                   → Γ ⊢C⦂ case+ inl V `inl M `inr N == M [ split-[] ↦ V ]c

    case+-beta-inr : ∀ {A B C}
                   → (V : Γ ⊢V⦂ B)
                   → (M : Γ ∷ A ⊢C⦂ C)
                   → (N : Γ ∷ B ⊢C⦂ C)
                   ----------------------------------------------------------
                   → Γ ⊢C⦂ case+ inr V `inl M `inr N == N [ split-[] ↦ V ]c

    -- eta-equation for sum elimination
    --
    -- Commuting conversions are instances of this rule.

    case+-eta : ∀ {A B C}
              → (V : Γ ⊢V⦂ A |+| B)
              → (M : Γ ∷ A |+| B ⊢C⦂ C)
              ------------------------------------------------------------------
              → Γ ⊢C⦂ case+ V
                        `inl (C-rename (cong-∷-ren wk-ren) M
                                [ split-[] ↦ inl (var (λ _ → ≾ᵣ-refl) Hd) ]c)
                        `inr (C-rename (cong-∷-ren wk-ren) M
                                [ split-[] ↦ inr (var (λ _ → ≾ᵣ-refl) Hd) ]c)
                  == M [ split-[] ↦ V ]c

    -- beta-equations for list elimination

    caseL-beta-nil : ∀ {A C}
                   → (M : Γ ⊢C⦂ C)
                   → (N : Γ ∷ A ∷ |List| A ⊢C⦂ C)
                   -----------------------------------------
                   → Γ ⊢C⦂ caseL nil `nil M `cons N == M

    caseL-beta-cons : ∀ {A C}
                    → (V : Γ ⊢V⦂ A)
                    → (W : Γ ⊢V⦂ |List| A)
                    → (M : Γ ⊢C⦂ C)
                    → (N : Γ ∷ A ∷ |List| A ⊢C⦂ C)
                    ----------------------------------------------
                    → Γ ⊢C⦂ caseL cons V W `nil M `cons N
                        == N [ split-[] ↦ V-rename wk-ren W ]c
                             [ split-[] ↦ V ]c

    -- eta-equation for list elimination
    --
    -- Commuting conversions are instances of this rule.

    caseL-eta : ∀ {A C}
              → (V : Γ ⊢V⦂ |List| A)
              → (M : Γ ∷ |List| A ⊢C⦂ C)
              -------------------------------------------------------------
              → Γ ⊢C⦂ caseL V
                        `nil (M [ split-[] ↦ nil ]c)
                        `cons ((C-rename (wk-ren ∘ʳ exch-ren ∘ʳ wk-ren ∘ʳ exch-ren) M)
                                 [ split-[] ↦ cons (var (λ _ → ≾ᵣ-refl) (Tl-∷ Hd))
                                                   (var (λ _ → ≾ᵣ-refl) Hd) ]c)
                  == M [ split-[] ↦ V ]c

    -- beta-equations for primitive recursion on lists; no eta-equation, as
    -- for `recℕ`

    recL-beta-nil : ∀ {A B ε}
                  → (M : Γ ⊢C⦂ B ‼ ε)
                  → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
                  → (p : ε ·ₑ ε ≾ₑ ε)
                  ---------------------------------------
                  → Γ ⊢C⦂ recL nil M N p == M

    recL-beta-cons : ∀ {A B ε}
                   → (V : Γ ⊢V⦂ A)
                   → (W : Γ ⊢V⦂ |List| A)
                   → (M : Γ ⊢C⦂ B ‼ ε)
                   → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ B ‼ ε)
                   → (p : ε ·ₑ ε ≾ₑ ε)
                   ------------------------------------------------------------
                   → Γ ⊢C⦂ recL (cons V W) M N p
                       == coerce p (recL W M N p ⨟ recL-step V W N)

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
                      == ε-≃ (≃ₑ-sym (·ₑ-identityˡ ε))
                           ((C-rename
                              (cong-∷-ren
                                (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren))
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
                       == ε-≃ (≃ₑ-sym (·ₑ-assoc (op-grade op) ε ε'))
                            (box _ (lam
                                   (handle M
                                   `with (λ op' ε'' →
                                            C-rename
                                              (cong-∷-ren (cong-∷-ren
                                                (barrier-wk-ren {Γ} (mapᵉ (op-grade op))
                                                                (type-of-gtype (arity op)))))
                                              (H op' ε''))
                                   `in (C-rename
                                         (cong-∷-ren
                                           ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ)
                                            ∘ʳ ⟨⟩-μ-ren)
                                            ∘ʳ cong-⟨⟩-ren wk-ren))
                                         N)))
                                  (C-rename (cong-∷-ren (cong-∷-ren barrier-ren))
                                    (H op (ε ·ₑ ε'))
                                   [ split-∷ split-[] ↦ V ]c))

    handle-delay : ∀ {A B τ ε ε'}
                 → (M : Γ ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε)
                 → (H : (op : Op) → (ε'' : E) →
                          Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                          ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ mapᵉ (of-durᵉ τ ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
                 ------------------------------------------------------------------------------
                 → Γ ⊢C⦂ handle delay τ M `with H `in N
                     == ε-≃ (≃ₑ-sym (·ₑ-assoc (of-durᵉ τ) ε ε'))
                          (delay τ
                            (handle M
                            `with (λ op' ε'' →
                                     C-rename (cong-∷-ren (cong-∷-ren
                                       (⟨⟩-≤-ren (≾-⊤ᵣ _) ∘ʳ ⟨⟩-μ-ren)))
                                       (H op' ε''))
                            `in (C-rename
                                  (cong-∷-ren
                                    (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ (≃ᵣ-trans map-·ᵉ (·ᵣ-cong map-of-durᵉ ≃ᵣ-refl)))
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
                 → Γ ⊢C⦂ handle box _ V M `with H `in N
                     == box _ V
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
               → Γ ⊢C⦂ box _ V (K [ unbox (∈-++ᶜˡ (hole-ctx K) Hd)
                                        (≾ᵣ-trans (≾ᵣ-reflexive
                                                    (grade-++ᶜˡ-uᵣ (hole-ctx K)))
                                                  p)
                                        w N ])
                   == box _ V (K [ N [ split-[] ↦ subV (V-rename ((cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-≤-ren p) ∘ʳ wk-ren-⟨ρ⟩-ctx refl) V) w ]c ])


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
             → Γ ⊢C⦂ box _ V
                     (box _ (V-rename (cong-⟨⟩-ren wk-ren) W) M)
                 == box _ W
                     (box _
                       (V-rename (cong-⟨⟩-ren wk-ren) V)
                       (C-rename exch-ren M))

    -- eta rule for box
    
    boxed-not-used : ∀ {A C ρ ε}
                   → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
                   → (M : Γ ⊢C⦂ C ‼ ε)
                   -----------------------------------
                   → Γ ⊢C⦂ box _ V (C-rename wk-ren M)
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
                   → Γ ⊢C⦂ box _ V
                            (unbox (Tl-∷ x₂) rel₂ w₂ M)
                       == unbox x₂ rel₂ w₂
                            (box _
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
               → (M : Γ ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε)
               ------------------------------------------------
               → Γ ⊢C⦂ subC (delay τ M) (w ‼ₛ ·ₑ-monoʳ-≾ₑ rel)
                    == delay τ (subC M (w ‼ₛ rel))

    -- Moving a scrutinee's subsumption outwards relaxes the continuation's
    -- lock along the effect half and subsumes its binder along the value half.
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
                       (M ⨟ subCtx w
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
                             `in (subCtx w
                                    (C-rename
                                      (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N)))

    -- `box` and `unbox` bind but compute nothing, so a subsumption of the
    -- node is a subsumption of the body, at an unrestricted witness.

    subC-box : ∀ {A C C' ρ}
             → (w : C <:ᶜ C')
             → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
             → (M : Γ ∷ [ ρ ] A ⊢C⦂ C)
             ----------------------------------------------------
             → Γ ⊢C⦂ subC (box _ V M) w == box _ V (subC M w)

    subC-unbox : ∀ {A A₀ C C' ρ₀ ρ'}
               → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
               → (rel : ρ' ≾ᵣ ρ₀)
               → (v : A₀ <:ᵛ A)
               → (w : C <:ᶜ C')
               → (M : Γ ∷ A ⊢C⦂ C)
               ----------------------------------------------------
               → Γ ⊢C⦂ subC (unbox x rel v M) w
                    == unbox x rel v (subC M w)

    -- Sub-effecting the result of a bind is sub-effecting its continuation.
    -- Only the effect half needs an axiom: its value half is derivable from
    -- the eta and associativity rules of `_⨟_`, this one is not.

    coerce-seq-in : ∀ {A B ε ε₁' ε₂'}
                  → (rel : ε₁' ≾ₑ ε₂')
                  → (M : Γ ⊢C⦂ A ‼ ε)
                  → (N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε₁')
                  ----------------------------------------------------------
                  → Γ ⊢C⦂ coerce (·ₑ-monoʳ-≾ₑ rel) (M ⨟ N) == M ⨟ coerce rel N

    -- Sub-effecting the answer of a `handle` is sub-effecting its return
    -- clause. Only the effect half moves: the handler's clauses are typed at
    -- the answer type, and their boxed continuation argument is contravariant
    -- in it.

    coerce-handle-in : ∀ {A B ε ε₁' ε₂'}
                     → (rel : ε₁' ≾ₑ ε₂')
                     → (M : Γ ⊢C⦂ A ‼ ε)
                     → (H : (op : Op) → (ε₀ : E) →
                              Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₀)
                              ⊢C⦂ B ‼ (op-grade op ·ₑ ε₀))
                     → (N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε₁')
                     ----------------------------------------------------------
                     → Γ ⊢C⦂ coerce (·ₑ-monoʳ-≾ₑ rel) (handle M `with H `in N)
                          == handle M `with H `in (coerce rel N)

    -- equations for collapsing successive delays

    delay-zero : ∀ {A ε}
               → (M : Γ ⟨ of-durʳ 0ᴰ ⟩ ⊢C⦂ A ‼ ε)
               --------------------------
               → Γ ⊢C⦂ delay 0ᴰ M
                   == ε-≃ (≃ₑ-sym (≃ₑ-trans (·ₑ-cong of-durᵉ-zero ≃ₑ-refl) (·ₑ-identityˡ ε)))
                        (C-rename
                          (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ of-durʳ-zero) ∘ʳ ⟨⟩-η-ren)
                          M)

    delay-delay : ∀ {A τ₁ τ₂ ε}
                → (M : Γ ⟨ of-durʳ (τ₁ +ᴰ τ₂) ⟩ ⊢C⦂ A ‼ ε)
                ------------------------------------
                → Γ ⊢C⦂ delay τ₁ (delay τ₂
                           (C-rename
                             (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ of-durʳ-plus) ∘ʳ ⟨⟩-μ-ren)
                             M))
                    == ε-≃ (≃ₑ-trans (·ₑ-cong of-durᵉ-plus ≃ₑ-refl) (·ₑ-assoc (of-durᵉ τ₁) (of-durᵉ τ₂) ε))
                         (delay (τ₁ +ᴰ τ₂) M)

  infix 18 _⊢C⦂_==_
