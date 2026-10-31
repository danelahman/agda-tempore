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

open import MonomorphicCalculus.Syntax.Renaming.Equivalence  S using (∈-++ᶜˡ; grade-++ᶜˡ-𝟏ᵣ)

-- Binder subsumption, shared with the two sequencing rules of the operational
-- semantics.

open import MonomorphicCalculus.Syntax.Substitution.Subsumption  S using (subCtx)


-- Equations between well-typed values and computations

mutual

  -- value equations

  data _⊢V⦂_≡ᵗʰ_ (Γ : Ctx) : {A : VType} → Γ ⊢V⦂ A → Γ ⊢V⦂ A → Set where

    -- reflexivity, symmetry, transitivity

    V-refl : ∀ {A}
           → {V : Γ ⊢V⦂ A}
           ---------------
           → Γ ⊢V⦂ V ≡ᵗʰ V

    V-sym : ∀ {A}
          → {V W : Γ ⊢V⦂ A}
          → Γ ⊢V⦂ V ≡ᵗʰ W
          -----------------
          → Γ ⊢V⦂ W ≡ᵗʰ V

    V-trans : ∀ {A}
            → {V W U : Γ ⊢V⦂ A}
            → Γ ⊢V⦂ V ≡ᵗʰ W
            → Γ ⊢V⦂ W ≡ᵗʰ U
            -------------------
            → Γ ⊢V⦂ V ≡ᵗʰ U

    -- substitutivity

    V-subst : ∀ {Γ' Γ₁ Γ₂ A B}
            → {V W : Γ' ⊢V⦂ B}
            → (p : Γ' ⊢V⦂ V ≡ᵗʰ W)
            → (s : Γ₁ ∷ A , Γ₂ split Γ')
            → (q : Γ₁ ++ᶜ Γ₂ ≡ Γ)
            → (U : Γ₁ ⊢V⦂ A)
            ---------------------------------------------------------------
            → Γ ⊢V⦂ subst (_⊢V⦂ B) q (V [ s ↦ U ]v)
                ≡ᵗʰ subst (_⊢V⦂ B) q (W [ s ↦ U ]v)

    -- congruence equations

    ⦉⦊-cong : ∀ {A B}
           → {V V' : Γ ⊢V⦂ A}
           → {W W' : Γ ⊢V⦂ B}
           → Γ ⊢V⦂ V ≡ᵗʰ V'
           → Γ ⊢V⦂ W ≡ᵗʰ W'
           ------------------------------
           → Γ ⊢V⦂ ⦉ V , W ⦊ ≡ᵗʰ ⦉ V' , W' ⦊

    succ-cong : {V V' : Γ ⊢V⦂ nat}
              → Γ ⊢V⦂ V ≡ᵗʰ V'
              ---------------------------
              → Γ ⊢V⦂ succ V ≡ᵗʰ succ V'

    inl-cong : ∀ {A B}
             → {V V' : Γ ⊢V⦂ A}
             → Γ ⊢V⦂ V ≡ᵗʰ V'
             --------------------------------------
             → Γ ⊢V⦂ inl {B = B} V ≡ᵗʰ inl {B = B} V'

    inr-cong : ∀ {A B}
             → {V V' : Γ ⊢V⦂ B}
             → Γ ⊢V⦂ V ≡ᵗʰ V'
             --------------------------------------
             → Γ ⊢V⦂ inr {A = A} V ≡ᵗʰ inr {A = A} V'

    cons-cong : ∀ {A}
              → {V V' : Γ ⊢V⦂ A}
              → {W W' : Γ ⊢V⦂ list A}
              → Γ ⊢V⦂ V ≡ᵗʰ V'
              → Γ ⊢V⦂ W ≡ᵗʰ W'
              ---------------------------------
              → Γ ⊢V⦂ cons V W ≡ᵗʰ cons V' W'

    fun-cong : ∀ {A B ε}
             → {M N : Γ ∷ A ⊢C⦂ B ! ε}
             → Γ ∷ A ⊢C⦂ M ≡ᵗʰ N
             -------------------------
             → Γ ⊢V⦂ fun M ≡ᵗʰ fun N

    handler-cong : ∀ {A B ε ε'}
                 → {N N' : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε'}
                 → {H H' : ((op : Op) → (ε'' : E) →
                              Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                                  ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                              ⊢C⦂ B ! (op-grade op ·ₑ ε''))}
                 → Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ N ≡ᵗʰ N'
                 → ((op : Op) → (ε'' : E) →
                      Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                          ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                      ⊢C⦂ H op ε'' ≡ᵗʰ H' op ε'')
                 ---------------------------------------------------
                 → Γ ⊢V⦂ handler N H ≡ᵗʰ handler N' H'

    -- eta equations

    unit-eta : (V : Γ ⊢V⦂ unit)
             ------------------
             → Γ ⊢V⦂ V ≡ᵗʰ ⋆

    fun-eta : ∀ {A C}
            → (V : Γ ⊢V⦂ A ⇒ C)
            -----------------------------------------------
            → Γ ⊢V⦂ V
                ≡ᵗʰ fun (V-rename wk-ren V · var (λ _ → ≾ᵣ-refl) Hd)

    -- equations for subsumption
    --
    -- Subsumption is erased, so it obeys exactly the laws of the coercion it
    -- denotes: witness irrelevance, and functoriality in the witness.

    subV-cong : ∀ {A A'}
              → {w w' : A <:ᵛ A'}
              → {V W : Γ ⊢V⦂ A}
              → Γ ⊢V⦂ V ≡ᵗʰ W
              ------------------------------
              → Γ ⊢V⦂ subV V w ≡ᵗʰ subV W w'

    subV-refl : ∀ {A}
              → (w : A <:ᵛ A)
              → (V : Γ ⊢V⦂ A)
              ----------------------
              → Γ ⊢V⦂ subV V w ≡ᵗʰ V

    subV-trans : ∀ {A₁ A₂ A₃}
               → (w : A₁ <:ᵛ A₂) → (w' : A₂ <:ᵛ A₃) → (w'' : A₁ <:ᵛ A₃)
               → (V : Γ ⊢V⦂ A₁)
               ------------------------------------------
               → Γ ⊢V⦂ subV (subV V w) w' ≡ᵗʰ subV V w''

    -- Subsumption is natural in the value formers: the witness splits the way
    -- its type does. At `⦉_,_⦊` that is functoriality of `_|×|_`, at `inl` and
    -- `inr` functoriality of `_|+|_`, at `nil` and `cons` functoriality of
    -- `list`, at `fun` functoriality of `_⇒_`, contravariant in the domain,
    -- so the binder is subsumed rather than the body coerced there. The atomic formers and `var` have no rule of their
    -- own.

    subV-pair : ∀ {A A' B B'}
              → (p : A <:ᵛ A') → (q : B <:ᵛ B')
              → (V : Γ ⊢V⦂ A)
              → (W : Γ ⊢V⦂ B)
              ------------------------------------------------------
              → Γ ⊢V⦂ subV ⦉ V , W ⦊ (p |×|ₛ q)
                   ≡ᵗʰ ⦉ subV V p , subV W q ⦊

    subV-inl : ∀ {A A' B B'}
             → (p : A <:ᵛ A') → (q : B <:ᵛ B')
             → (V : Γ ⊢V⦂ A)
             ---------------------------------------------------
             → Γ ⊢V⦂ subV (inl V) (p |+|ₛ q) ≡ᵗʰ inl (subV V p)

    subV-inr : ∀ {A A' B B'}
             → (p : A <:ᵛ A') → (q : B <:ᵛ B')
             → (V : Γ ⊢V⦂ B)
             ---------------------------------------------------
             → Γ ⊢V⦂ subV (inr V) (p |+|ₛ q) ≡ᵗʰ inr (subV V q)

    subV-nil : ∀ {A A'}
             → (p : A <:ᵛ A')
             ---------------------------------------------
             → Γ ⊢V⦂ subV (nil {A = A}) (listₛ p) ≡ᵗʰ nil

    subV-cons : ∀ {A A'}
              → (p : A <:ᵛ A')
              → (V : Γ ⊢V⦂ A)
              → (W : Γ ⊢V⦂ list A)
              ------------------------------------------------------------
              → Γ ⊢V⦂ subV (cons V W) (listₛ p)
                   ≡ᵗʰ cons (subV V p) (subV W (listₛ p))

    subV-fun : ∀ {A A' C C'}
             → (p : A' <:ᵛ A)
             → (w : C <:ᶜ C')
             → (M : Γ ∷ A ⊢C⦂ C)
             ------------------------------------------------------
             → Γ ⊢V⦂ subV (fun M) (p ⇒ₛ w)
                  ≡ᵗʰ fun (subC (subCtx p M) w)

  infix 18 _⊢V⦂_≡ᵗʰ_

  -- computation equations

  data _⊢C⦂_≡ᵗʰ_ (Γ : Ctx) : {C : CType} → Γ ⊢C⦂ C → Γ ⊢C⦂ C → Set where

    -- reflexivity, symmetry, transitivity

    C-refl : ∀ {C}
           → {M : Γ ⊢C⦂ C}
           ---------------
           → Γ ⊢C⦂ M ≡ᵗʰ M

    C-sym : ∀ {C}
          → {M N : Γ ⊢C⦂ C}
          → Γ ⊢C⦂ M ≡ᵗʰ N
          -----------------
          → Γ ⊢C⦂ N ≡ᵗʰ M

    C-trans : ∀ {C}
            → {M N P : Γ ⊢C⦂ C}
            → Γ ⊢C⦂ M ≡ᵗʰ N
            → Γ ⊢C⦂ N ≡ᵗʰ P
            -------------------
            → Γ ⊢C⦂ M ≡ᵗʰ P

    -- substitutivity

    C-subst : ∀ {Γ' Γ₁ Γ₂ A C}
            → {M N : Γ' ⊢C⦂ C}
            → (p : Γ' ⊢C⦂ M ≡ᵗʰ N)
            → (s : Γ₁ ∷ A , Γ₂ split Γ')
            → (q : Γ₁ ++ᶜ Γ₂ ≡ Γ)
            → (V : Γ₁ ⊢V⦂ A)
            ---------------------------------------------------------------
            → Γ ⊢C⦂ subst (_⊢C⦂ C) q (M [ s ↦ V ]c)
                ≡ᵗʰ subst (_⊢C⦂ C) q (N [ s ↦ V ]c)

    -- congruence equations

    return-cong : ∀ {A}
                → {V W : Γ ⊢V⦂ A}
                → Γ ⊢V⦂ V ≡ᵗʰ W
                ----------------------------
                → Γ ⊢C⦂ return V ≡ᵗʰ return W

    seq-cong : ∀ {A B ε ε'}
             → {M M' : Γ ⊢C⦂ A ! ε}
             → {N N' : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε'}
             → Γ ⊢C⦂ M ≡ᵗʰ M'
             → Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ N ≡ᵗʰ N'
             ---------------------------------
             → Γ ⊢C⦂ M ⨟ N ≡ᵗʰ M' ⨟ N'

    app-cong : ∀ {A C}
             → {V V' : Γ ⊢V⦂ A ⇒ C}
             → {W W' : Γ ⊢V⦂ A}
             → Γ ⊢V⦂ V ≡ᵗʰ V'
             → Γ ⊢V⦂ W ≡ᵗʰ W'
             ------------------------
             → Γ ⊢C⦂ V · W ≡ᵗʰ V' · W'

    match-cong : ∀ {A B C}
               → {V W : Γ ⊢V⦂ A |×| B}
               → {M N : Γ ∷ A ∷ B ⊢C⦂ C}
               → Γ ⊢V⦂ V ≡ᵗʰ W
               → Γ ∷ A ∷ B ⊢C⦂ M ≡ᵗʰ N
               --------------------------------------
               → Γ ⊢C⦂ match V `with M ≡ᵗʰ match W `with N

    absurd-cong : ∀ {C}
                → {V W : Γ ⊢V⦂ empty}
                → Γ ⊢V⦂ V ≡ᵗʰ W
                ------------------------------------
                → Γ ⊢C⦂ absurd {C = C} V ≡ᵗʰ absurd {C = C} W

    cmp-cong : ∀ {A ⋈}
             → {V V' W W' : Γ ⊢V⦂ A}
             → {et : Et A}
             → Γ ⊢V⦂ V ≡ᵗʰ V'
             → Γ ⊢V⦂ W ≡ᵗʰ W'
             ------------------------------------------
             → Γ ⊢C⦂ cmp ⋈ V W et ≡ᵗʰ cmp ⋈ V' W' et

    if-cong : ∀ {C}
            → {V W : Γ ⊢V⦂ bool}
            → {M M' N N' : Γ ⊢C⦂ C}
            → Γ ⊢V⦂ V ≡ᵗʰ W
            → Γ ⊢C⦂ M ≡ᵗʰ M'
            → Γ ⊢C⦂ N ≡ᵗʰ N'
            ----------------------------------------------------------
            → Γ ⊢C⦂ if V `then M `else N ≡ᵗʰ if W `then M' `else N'

    matchℕ-cong : ∀ {C}
                → {V W : Γ ⊢V⦂ nat}
                → {M M' : Γ ⊢C⦂ C}
                → {N N' : Γ ∷ nat ⊢C⦂ C}
                → Γ ⊢V⦂ V ≡ᵗʰ W
                → Γ ⊢C⦂ M ≡ᵗʰ M'
                → Γ ∷ nat ⊢C⦂ N ≡ᵗʰ N'
                --------------------------------------------------------------
                → Γ ⊢C⦂ matchℕ V `zero M `succ N ≡ᵗʰ matchℕ W `zero M' `succ N'

    recℕ-cong : ∀ {B ε}
              → {V W : Γ ⊢V⦂ nat}
              → {M M' : Γ ⊢C⦂ B ! ε}
              → {N N' : (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε}
              → {p : ε ·ₑ ε ≾ₑ ε}
              → Γ ⊢V⦂ V ≡ᵗʰ W
              → Γ ⊢C⦂ M ≡ᵗʰ M'
              → (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ N ≡ᵗʰ N'
              -----------------------------------------------
              → Γ ⊢C⦂ recℕ V M N p ≡ᵗʰ recℕ W M' N' p

    matchL-cong : ∀ {A C}
                → {V W : Γ ⊢V⦂ list A}
                → {M M' : Γ ⊢C⦂ C}
                → {N N' : Γ ∷ A ∷ list A ⊢C⦂ C}
                → Γ ⊢V⦂ V ≡ᵗʰ W
                → Γ ⊢C⦂ M ≡ᵗʰ M'
                → Γ ∷ A ∷ list A ⊢C⦂ N ≡ᵗʰ N'
                ------------------------------------------------------------
                → Γ ⊢C⦂ matchL V `nil M `cons N ≡ᵗʰ matchL W `nil M' `cons N'

    recL-cong : ∀ {A B ε}
              → {V W : Γ ⊢V⦂ list A}
              → {M M' : Γ ⊢C⦂ B ! ε}
              → {N N' : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε}
              → {p : ε ·ₑ ε ≾ₑ ε}
              → Γ ⊢V⦂ V ≡ᵗʰ W
              → Γ ⊢C⦂ M ≡ᵗʰ M'
              → (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ N ≡ᵗʰ N'
              ---------------------------------------------------------
              → Γ ⊢C⦂ recL V M N p ≡ᵗʰ recL W M' N' p

    match+-cong : ∀ {A B C}
                → {V W : Γ ⊢V⦂ A |+| B}
                → {M M' : Γ ∷ A ⊢C⦂ C}
                → {N N' : Γ ∷ B ⊢C⦂ C}
                → Γ ⊢V⦂ V ≡ᵗʰ W
                → Γ ∷ A ⊢C⦂ M ≡ᵗʰ M'
                → Γ ∷ B ⊢C⦂ N ≡ᵗʰ N'
                ------------------------------------------------------------
                → Γ ⊢C⦂ match+ V `inl M `inr N ≡ᵗʰ match+ W `inl M' `inr N'

    perform-cong : ∀ {A ε op}
                 → {V W : Γ ⊢V⦂ ⌜ param op ⌝ᵍ}
                 → {M N : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A ! ε}
                 → Γ ⊢V⦂ V ≡ᵗʰ W
                 → Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ M ≡ᵗʰ N
                 ---------------------------------------------------------------
                 → Γ ⊢C⦂ perform op V M ≡ᵗʰ perform op W N

    delay-cong  : ∀ {A τ ε}
                → {M N : Γ ⟨ ιᵣ τ ⟩ ⊢C⦂ A ! ε}
                → Γ ⟨ ιᵣ τ ⟩ ⊢C⦂ M ≡ᵗʰ N
                --------------------------------------
                → Γ ⊢C⦂ delay τ M ≡ᵗʰ delay τ N

    handle-cong : ∀ {A B ε ε'}
                → {M M' : Γ ⊢C⦂ A ! ε}
                → {V V' : Γ ⊢V⦂ (A ! ε) ⇛ (B ! ε')}
                → Γ ⊢C⦂ M ≡ᵗʰ M'
                → Γ ⊢V⦂ V ≡ᵗʰ V'
                -----------------------------------------------
                → Γ ⊢C⦂ handle M `with V ≡ᵗʰ handle M' `with V'

    -- The grade bound and the payload subsumption an `unbox` stores are both
    -- irrelevant, so the two nodes are compared at the resource variable they
    -- name.

    unbox-cong : ∀ {A A₀ C ρ₀ ρ'}
               → {x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ}
               → {rel rel' : ρ' ≾ᵣ ρ₀}
               → {w w' : A₀ <:ᵛ A}
               → {M N : Γ ∷ A  ⊢C⦂ C}
               → Γ ∷ A ⊢C⦂ M ≡ᵗʰ N
               ------------------------------------------------
               → Γ ⊢C⦂ unbox x rel w M ≡ᵗʰ unbox x rel' w' N

    box-cong : ∀ {A C ρ}
             → {V W : Γ ⟨ ρ ⟩ ⊢V⦂ A}
             → {M N : Γ ∷ [ ρ ] A ⊢C⦂ C}
             → Γ ⟨ ρ ⟩ ⊢V⦂ V ≡ᵗʰ W
             → Γ ∷ [ ρ ] A ⊢C⦂ M ≡ᵗʰ N
             --------------------------
             → Γ ⊢C⦂ box _ V M ≡ᵗʰ box _ W N

    subC-cong : ∀ {C C'}
              → {w w' : C <:ᶜ C'}
              → {M N : Γ ⊢C⦂ C}
              → Γ ⊢C⦂ M ≡ᵗʰ N
              ------------------------------
              → Γ ⊢C⦂ subC M w ≡ᵗʰ subC N w'

    -- computational/beta-equations for sequential composition

    seq-return : ∀ {A B ε}
               → (V : Γ ⊢V⦂ A)
               → (M : Γ ⟨ ∣ 𝟏ₑ ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε)
               -----------------------------------------------------
               → Γ ⊢C⦂ return V ⨟ M
                   ≡ᵗʰ ε-≃ (≃ₑ-sym (·ₑ-identityˡ ε))
                        ((C-rename
                           (cong-∷-ren
                             (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-𝟏ᵉ) ∘ʳ ⟨⟩-η-ren))
                           M)
                         [ split-[] ↦ V ]c)

    seq-perform : ∀ {A B ε ε' op}
                → (V : Γ ⊢V⦂ ⌜ param op ⌝ᵍ)
                → (M : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A ! ε)
                → (N : Γ ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε')
                ---------------------------------------------------------------------
                → Γ ⊢C⦂ (perform op V M) ⨟ N
                    ≡ᵗʰ ε-≃ (≃ₑ-sym (·ₑ-assoc (op-grade op) ε ε'))
                         (perform op V
                            (M ⨟
                             C-rename
                               (cong-∷-ren
                                 ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ)
                                  ∘ʳ ⟨⟩-μ-ren)
                                  ∘ʳ cong-⟨⟩-ren wk-ren))
                               N))

    seq-delay : ∀ {A B τ ε ε'}
              → (M : Γ ⟨ ιᵣ τ ⟩ ⊢C⦂ A ! ε)
              → (N : Γ ⟨ ∣ ιₑ τ ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε')
              -------------------------------------------------------
              → Γ ⊢C⦂ delay τ M ⨟ N
                  ≡ᵗʰ ε-≃ (≃ₑ-sym (·ₑ-assoc (ιₑ τ) ε ε'))
                       (delay τ
                         (M ⨟
                          C-rename
                            (cong-∷-ren
                              (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ (≃ᵣ-trans map-·ᵉ (·ᵣ-cong map-ιᵉ ≃ᵣ-refl)))
                               ∘ʳ ⟨⟩-μ-ren))
                            N))

    seq-box : ∀ {A B C ρ ε ε'}
            → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
            → (M : Γ ∷ [ ρ ] A ⊢C⦂ B ! ε)
            → (N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ C ! ε')
            -------------------------------------------------------
            → Γ ⊢C⦂ box _ V M ⨟ N
                ≡ᵗʰ box _ V (M ⨟ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N)

    seq-unbox : ∀ {A A₀ B C ρ₀ ρ' ε ε'}
              → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
              → (rel : ρ' ≾ᵣ ρ₀)
              → (w : A₀ <:ᵛ A)
              → (M : Γ ∷ A ⊢C⦂ B ! ε)
              → (N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ C ! ε')
              -------------------------------------------------------
              → Γ ⊢C⦂ unbox x rel w M ⨟ N
                  ≡ᵗʰ unbox x rel w (M ⨟ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N)

    -- eta-equation for sequential composition

    seq-eta : ∀ {A ε}
            → (M : Γ ⊢C⦂ A ! ε)
            ----------------------------------------------------------
            → Γ ⊢C⦂ M
                ≡ᵗʰ ε-≃ (·ₑ-identityʳ ε) (M ⨟ return (var (λ _ → ≾ᵣ-refl) Hd))

    -- associativity equation for sequential composition

    seq-assoc : ∀ {A B C ε ε' ε''}
              → (M : Γ ⊢C⦂ A ! ε)
              → (N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε')
              → (P : Γ ⟨ ∣ ε ·ₑ ε' ∣ᵉ ⟩ ∷ B ⊢C⦂ C ! ε'')
              ---------------------------------------------------------------------
              → Γ ⊢C⦂ (M ⨟ N) ⨟ P
                  ≡ᵗʰ ε-≃ (≃ₑ-sym (·ₑ-assoc ε ε' ε''))
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
             → Γ ⊢C⦂ fun M · W
                 ≡ᵗʰ M [ split-[] ↦ W ]c

    -- beta-equation for pattern-matching

    match-beta : ∀ {A B C}
               → (V : Γ ⊢V⦂ A)
               → (W : Γ ⊢V⦂ B)
               → (M : Γ ∷ A ∷ B ⊢C⦂ C)
               ------------------------------------
               → Γ ⊢C⦂ match ⦉ V , W ⦊ `with M
                   ≡ᵗʰ M [ split-[] ↦ V-rename wk-ren W ]c
                         [ split-[] ↦ V ]c

    -- eta-equation for pattern-matching

    match-eta : ∀ {A B C}
              → (V : Γ ⊢V⦂ A |×| B)
              → (M : Γ ∷ A |×| B ⊢C⦂ C)
              -------------------------------------------------------------
              → Γ ⊢C⦂ match V `with
                       ((C-rename (wk-ren ∘ʳ exch-ren ∘ʳ wk-ren ∘ʳ exch-ren)
                         M) [ split-[] ↦ ⦉ var (λ _ → ≾ᵣ-refl) (Tl-∷ Hd) , var (λ _ → ≾ᵣ-refl) Hd ⦊ ]c)
                  ≡ᵗʰ M [ split-[] ↦ V ]c

    -- eta-equation for empty type elimination

    absurd-eta : ∀ {C}
               → (V : Γ ⊢V⦂ empty)
               → (M : Γ ∷ empty ⊢C⦂ C)
               -----------------------
               → Γ ⊢C⦂ absurd {C = C} V
                   ≡ᵗʰ M [ split-[] ↦ V ]c

    -- beta-equation for comparison: at data, the relation's truth on their
    -- order

    cmp-beta : ∀ {A}
             → (⋈ : Cmp)
             → (et : Et A)
             → (d e : ⟪ A ⟫)
             ---------------------------------------------------------------
             → Γ ⊢C⦂ cmp ⋈ (⌈ et ⌉ d) (⌈ et ⌉ e) et
                 ≡ᵗʰ return ⌈ holds ⋈ (compareᵈ et d e) ⌉ᵇ

    -- beta-equations for boolean elimination

    if-beta-true : ∀ {C}
                 → (M N : Γ ⊢C⦂ C)
                 -----------------------------------------
                 → Γ ⊢C⦂ if true `then M `else N ≡ᵗʰ M

    if-beta-false : ∀ {C}
                  → (M N : Γ ⊢C⦂ C)
                  -----------------------------------------
                  → Γ ⊢C⦂ if false `then M `else N ≡ᵗʰ N

    -- eta-equation for boolean elimination
    --
    -- Commuting conversions are instances of this rule.

    if-eta : ∀ {C}
           → (V : Γ ⊢V⦂ bool)
           → (M : Γ ∷ bool ⊢C⦂ C)
           ------------------------------------------------------
           → Γ ⊢C⦂ if V `then (M [ split-[] ↦ true  ]c)
                        `else (M [ split-[] ↦ false ]c)
               ≡ᵗʰ M [ split-[] ↦ V ]c

    -- beta-equations for natural-number elimination

    matchℕ-beta-zero : ∀ {C}
                     → (M : Γ ⊢C⦂ C)
                     → (N : Γ ∷ nat ⊢C⦂ C)
                     -------------------------------------------
                     → Γ ⊢C⦂ matchℕ zero `zero M `succ N ≡ᵗʰ M

    matchℕ-beta-succ : ∀ {C}
                     → (V : Γ ⊢V⦂ nat)
                     → (M : Γ ⊢C⦂ C)
                     → (N : Γ ∷ nat ⊢C⦂ C)
                     -------------------------------------------------------------
                     → Γ ⊢C⦂ matchℕ succ V `zero M `succ N ≡ᵗʰ N [ split-[] ↦ V ]c

    -- eta-equation for natural-number elimination
    --
    -- Commuting conversions are instances of this rule.

    matchℕ-eta : ∀ {C}
               → (V : Γ ⊢V⦂ nat)
               → (M : Γ ∷ nat ⊢C⦂ C)
               ------------------------------------------------------------------
               → Γ ⊢C⦂ matchℕ V
                        `zero (M [ split-[] ↦ zero ]c)
                        `succ (C-rename (cong-∷-ren wk-ren) M
                                [ split-[] ↦ succ (var (λ _ → ≾ᵣ-refl) Hd) ]c)
                   ≡ᵗʰ M [ split-[] ↦ V ]c

    -- beta-equations for primitive recursion
    --
    -- There is no eta-equation: the recursor's uniqueness is an induction
    -- principle over the scrutinee, not an equation between two terms.

    recℕ-beta-zero : ∀ {B ε}
                   → (M : Γ ⊢C⦂ B ! ε)
                   → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε)
                   → (p : ε ·ₑ ε ≾ₑ ε)
                   ---------------------------------------
                   → Γ ⊢C⦂ recℕ zero M N p ≡ᵗʰ M

    recℕ-beta-succ : ∀ {B ε}
                   → (V : Γ ⊢V⦂ nat)
                   → (M : Γ ⊢C⦂ B ! ε)
                   → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε)
                   → (p : ε ·ₑ ε ≾ₑ ε)
                   ------------------------------------------------------------
                   → Γ ⊢C⦂ recℕ (succ V) M N p
                       ≡ᵗʰ coerce p (recℕ V M N p ⨟ recℕ-step V N)

    -- beta-equations for sum elimination

    match+-beta-inl : ∀ {A B C}
                    → (V : Γ ⊢V⦂ A)
                    → (M : Γ ∷ A ⊢C⦂ C)
                    → (N : Γ ∷ B ⊢C⦂ C)
                    ----------------------------------------------------------
                    → Γ ⊢C⦂ match+ inl V `inl M `inr N ≡ᵗʰ M [ split-[] ↦ V ]c

    match+-beta-inr : ∀ {A B C}
                    → (V : Γ ⊢V⦂ B)
                    → (M : Γ ∷ A ⊢C⦂ C)
                    → (N : Γ ∷ B ⊢C⦂ C)
                    ----------------------------------------------------------
                    → Γ ⊢C⦂ match+ inr V `inl M `inr N ≡ᵗʰ N [ split-[] ↦ V ]c

    -- eta-equation for sum elimination
    --
    -- Commuting conversions are instances of this rule.

    match+-eta : ∀ {A B C}
               → (V : Γ ⊢V⦂ A |+| B)
               → (M : Γ ∷ A |+| B ⊢C⦂ C)
               ------------------------------------------------------------------
               → Γ ⊢C⦂ match+ V
                        `inl (C-rename (cong-∷-ren wk-ren) M
                                [ split-[] ↦ inl (var (λ _ → ≾ᵣ-refl) Hd) ]c)
                        `inr (C-rename (cong-∷-ren wk-ren) M
                                [ split-[] ↦ inr (var (λ _ → ≾ᵣ-refl) Hd) ]c)
                   ≡ᵗʰ M [ split-[] ↦ V ]c

    -- beta-equations for list elimination

    matchL-beta-nil : ∀ {A C}
                    → (M : Γ ⊢C⦂ C)
                    → (N : Γ ∷ A ∷ list A ⊢C⦂ C)
                    -----------------------------------------
                    → Γ ⊢C⦂ matchL nil `nil M `cons N ≡ᵗʰ M

    matchL-beta-cons : ∀ {A C}
                     → (V : Γ ⊢V⦂ A)
                     → (W : Γ ⊢V⦂ list A)
                     → (M : Γ ⊢C⦂ C)
                     → (N : Γ ∷ A ∷ list A ⊢C⦂ C)
                     ----------------------------------------------
                     → Γ ⊢C⦂ matchL cons V W `nil M `cons N
                         ≡ᵗʰ N [ split-[] ↦ V-rename wk-ren W ]c
                               [ split-[] ↦ V ]c

    -- eta-equation for list elimination
    --
    -- Commuting conversions are instances of this rule.

    matchL-eta : ∀ {A C}
               → (V : Γ ⊢V⦂ list A)
               → (M : Γ ∷ list A ⊢C⦂ C)
               -------------------------------------------------------------
               → Γ ⊢C⦂ matchL V
                        `nil (M [ split-[] ↦ nil ]c)
                        `cons ((C-rename (wk-ren ∘ʳ exch-ren ∘ʳ wk-ren ∘ʳ exch-ren) M)
                                 [ split-[] ↦ cons (var (λ _ → ≾ᵣ-refl) (Tl-∷ Hd))
                                                   (var (λ _ → ≾ᵣ-refl) Hd) ]c)
                   ≡ᵗʰ M [ split-[] ↦ V ]c

    -- beta-equations for primitive recursion on lists; no eta-equation, as
    -- for `recℕ`

    recL-beta-nil : ∀ {A B ε}
                  → (M : Γ ⊢C⦂ B ! ε)
                  → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε)
                  → (p : ε ·ₑ ε ≾ₑ ε)
                  ---------------------------------------
                  → Γ ⊢C⦂ recL nil M N p ≡ᵗʰ M

    recL-beta-cons : ∀ {A B ε}
                   → (V : Γ ⊢V⦂ A)
                   → (W : Γ ⊢V⦂ list A)
                   → (M : Γ ⊢C⦂ B ! ε)
                   → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢C⦂ B ! ε)
                   → (p : ε ·ₑ ε ≾ₑ ε)
                   ------------------------------------------------------------
                   → Γ ⊢C⦂ recL (cons V W) M N p
                       ≡ᵗʰ coerce p (recL W M N p ⨟ recL-step V W N)

    -- computational/beta-equations for effect handling
    --
    -- `return`, `perform` and `delay` are handled by a handler literal, whose
    -- clause family is re-barred across the binder or lock the handle moves
    -- under. The binders `box` and `unbox` commute with handling by any
    -- handler value, weakened past them. Handler values have no η-law.

    handle-return : ∀ {A B ε}
                  → (V : Γ ⊢V⦂ A)
                  → (H : (op : Op) → (ε'' : E) →
                           Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                               ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                           ⊢C⦂ B ! (op-grade op ·ₑ ε''))
                  → (N : Γ ⟨ ∣ 𝟏ₑ ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε)
                  ----------------------------------------------------------------
                  → Γ ⊢C⦂ handle return V `with handler N H
                      ≡ᵗʰ ε-≃ (≃ₑ-sym (·ₑ-identityˡ ε))
                           ((C-rename
                              (cong-∷-ren
                                (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-𝟏ᵉ) ∘ʳ ⟨⟩-η-ren))
                              N)
                            [ split-[] ↦ V ]c)

    handle-perform : ∀ {A B ε ε' op}
                   → (V : Γ ⊢V⦂ ⌜ param op ⌝ᵍ)
                   → (M : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A ! ε)
                   → (H : (op : Op) → (ε'' : E) →
                            Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                                ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                            ⊢C⦂ B ! (op-grade op ·ₑ ε''))
                   → (N : Γ ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε')
                   ----------------------------------------------------------------
                   → Γ ⊢C⦂ handle perform op V M `with handler N H
                       ≡ᵗʰ ε-≃ (≃ₑ-sym (·ₑ-assoc (op-grade op) ε ε'))
                            (box _ (fun
                                   (handle M
                                   `with handler
                                           (C-rename
                                             (cong-∷-ren
                                               ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ)
                                                ∘ʳ ⟨⟩-μ-ren)
                                                ∘ʳ cong-⟨⟩-ren wk-ren))
                                             N)
                                           (λ op' ε'' →
                                              C-rename
                                                (cong-∷-ren (cong-∷-ren
                                                  (barrier-wk-ren {Γ} ∣ op-grade op ∣ᵉ
                                                                  ⌜ arity op ⌝ᵍ)))
                                                (H op' ε''))))
                                  (C-rename (cong-∷-ren (cong-∷-ren barrier-ren))
                                    (H op (ε ·ₑ ε'))
                                   [ split-∷ split-[] ↦ V ]c))

    handle-delay : ∀ {A B τ ε ε'}
                 → (M : Γ ⟨ ιᵣ τ ⟩ ⊢C⦂ A ! ε)
                 → (H : (op : Op) → (ε'' : E) →
                          Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                              ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                          ⊢C⦂ B ! (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ ∣ ιₑ τ ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε')
                 ------------------------------------------------------------------------------
                 → Γ ⊢C⦂ handle delay τ M `with handler N H
                     ≡ᵗʰ ε-≃ (≃ₑ-sym (·ₑ-assoc (ιₑ τ) ε ε'))
                          (delay τ
                            (handle M
                            `with handler
                                    (C-rename
                                      (cong-∷-ren
                                        (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ (≃ᵣ-trans map-·ᵉ (·ᵣ-cong map-ιᵉ ≃ᵣ-refl)))
                                         ∘ʳ ⟨⟩-μ-ren))
                                      N)
                                    (λ op' ε'' →
                                       C-rename (cong-∷-ren (cong-∷-ren
                                         (⟨⟩-≤-ren (≾-⊤ᵣ _) ∘ʳ ⟨⟩-μ-ren)))
                                         (H op' ε''))))

    handle-box : ∀ {A B C ρ ε ε'}
               → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
               → (M : Γ ∷ [ ρ ] A ⊢C⦂ B ! ε)
               → (W : Γ ⊢V⦂ (B ! ε) ⇛ (C ! ε'))
               ------------------------------------------------------------
               → Γ ⊢C⦂ handle box _ V M `with W
                   ≡ᵗʰ box _ V (handle M `with V-rename wk-ren W)

    handle-unbox : ∀ {A A₀ B C ρ₀ ρ' ε ε'}
                 → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
                 → (rel : ρ' ≾ᵣ ρ₀)
                 → (w : A₀ <:ᵛ A)
                 → (M : Γ ∷ A ⊢C⦂ B ! ε)
                 → (V : Γ ⊢V⦂ (B ! ε) ⇛ (C ! ε'))
                 ------------------------------------------------------------
                 → Γ ⊢C⦂ handle unbox x rel w M `with V
                     ≡ᵗʰ unbox x rel w (handle M `with V-rename wk-ren V)

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
                                                    (grade-++ᶜˡ-𝟏ᵣ (hole-ctx K)))
                                                  p)
                                        w N ])
                   ≡ᵗʰ box _ V (K [ N [ split-[] ↦ subV (V-rename ((cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-≤-ren p) ∘ʳ wk-ren-⟨ρ⟩-ctx refl) V) w ]c ])


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
                   ≡ᵗʰ unbox x₂ rel₂ w₂
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
                 ≡ᵗʰ box _ W
                     (box _
                       (V-rename (cong-⟨⟩-ren wk-ren) V)
                       (C-rename exch-ren M))

    -- eta rule for box
    
    boxed-not-used : ∀ {A C ρ ε}
                   → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
                   → (M : Γ ⊢C⦂ C ! ε)
                   -----------------------------------
                   → Γ ⊢C⦂ box _ V (C-rename wk-ren M)
                       ≡ᵗʰ M

    -- eta rule for unbox

    unbox-not-used : ∀ {A A₀ C ρ₀ ρ'}
                   → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
                   → (rel : ρ' ≾ᵣ ρ₀)
                   → (w : A₀ <:ᵛ A)
                   → (M : Γ ⊢C⦂ C)
                   ---------------------------------------------------
                   → Γ ⊢C⦂ unbox x rel w (C-rename (wk-ren {A = A}) M)
                       ≡ᵗʰ M

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
                       ≡ᵗʰ unbox x₂ rel₂ w₂
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
              → Γ ⊢C⦂ subC M w ≡ᵗʰ M

    subC-trans : ∀ {C₁ C₂ C₃}
               → (w : C₁ <:ᶜ C₂) → (w' : C₂ <:ᶜ C₃) → (w'' : C₁ <:ᶜ C₃)
               → (M : Γ ⊢C⦂ C₁)
               ----------------------------------------------
               → Γ ⊢C⦂ subC (subC M w) w' ≡ᵗʰ subC M w''

    subC-perform : ∀ {A A' ε ε' op}
                 → (w : A <:ᵛ A')
                 → (rel : ε ≾ₑ ε')
                 → (V : Γ ⊢V⦂ ⌜ param op ⌝ᵍ)
                 → (M : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
                        ⊢C⦂ A ! ε)
                 ----------------------------------------------------------
                 → Γ ⊢C⦂ subC (perform op V M) (w !ₛ ·ₑ-monoʳ-≾ₑ rel)
                      ≡ᵗʰ perform op V (subC M (w !ₛ rel))

    subC-delay : ∀ {A A' τ ε ε'}
               → (w : A <:ᵛ A')
               → (rel : ε ≾ₑ ε')
               → (M : Γ ⟨ ιᵣ τ ⟩ ⊢C⦂ A ! ε)
               ------------------------------------------------
               → Γ ⊢C⦂ subC (delay τ M) (w !ₛ ·ₑ-monoʳ-≾ₑ rel)
                    ≡ᵗʰ delay τ (subC M (w !ₛ rel))

    -- Moving a scrutinee's subsumption outwards relaxes the continuation's
    -- lock along the effect half and subsumes its binder along the value half.
    -- For `handle` both halves move onto the handler value. Neither `_⨟_` nor
    -- `handle_`with_` carries a payload witness of its own, as `unbox` does.

    subC-seq : ∀ {A A' B ε₁ ε₂ ε'}
             → (w : A <:ᵛ A')
             → (rel : ε₁ ≾ₑ ε₂)
             → (M : Γ ⊢C⦂ A ! ε₁)
             → (N : Γ ⟨ ∣ ε₂ ∣ᵉ ⟩ ∷ A' ⊢C⦂ B ! ε')
             ------------------------------------------------------------
             → Γ ⊢C⦂ subC M (w !ₛ rel) ⨟ N
                  ≡ᵗʰ coerce (·ₑ-monoˡ-≾ₑ rel)
                       (M ⨟ subCtx w
                              (C-rename
                                (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N))

    subC-handle : ∀ {A A' B ε₁ ε₂ ε'}
                → (w : A <:ᵛ A')
                → (rel : ε₁ ≾ₑ ε₂)
                → (M : Γ ⊢C⦂ A ! ε₁)
                → (V : Γ ⊢V⦂ (A' ! ε₂) ⇛ (B ! ε'))
                ----------------------------------------------------------------
                → Γ ⊢C⦂ handle (subC M (w !ₛ rel)) `with V
                     ≡ᵗʰ coerce (·ₑ-monoˡ-≾ₑ rel)
                          (handle M `with subV V ((w !ₛ rel) ⇛ₛ <:ᶜ-refl (B ! ε')))

    -- `box` and `unbox` bind but compute nothing, so a subsumption of the
    -- node is a subsumption of the body, at an unrestricted witness.

    subC-box : ∀ {A C C' ρ}
             → (w : C <:ᶜ C')
             → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
             → (M : Γ ∷ [ ρ ] A ⊢C⦂ C)
             ----------------------------------------------------
             → Γ ⊢C⦂ subC (box _ V M) w ≡ᵗʰ box _ V (subC M w)

    subC-unbox : ∀ {A A₀ C C' ρ₀ ρ'}
               → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
               → (rel : ρ' ≾ᵣ ρ₀)
               → (v : A₀ <:ᵛ A)
               → (w : C <:ᶜ C')
               → (M : Γ ∷ A ⊢C⦂ C)
               ----------------------------------------------------
               → Γ ⊢C⦂ subC (unbox x rel v M) w
                    ≡ᵗʰ unbox x rel v (subC M w)

    -- Sub-effecting the result of a bind is sub-effecting its continuation.
    -- Only the effect half needs an axiom: its value half is derivable from
    -- the eta and associativity rules of `_⨟_`, this one is not.

    coerce-seq-in : ∀ {A B ε ε₁' ε₂'}
                  → (rel : ε₁' ≾ₑ ε₂')
                  → (M : Γ ⊢C⦂ A ! ε)
                  → (N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε₁')
                  ----------------------------------------------------------
                  → Γ ⊢C⦂ coerce (·ₑ-monoʳ-≾ₑ rel) (M ⨟ N) ≡ᵗʰ M ⨟ coerce rel N

    -- Handling with a coerced handler value coerces the handled computation
    -- in and the answer out. The handled grade stays fixed: restricting it
    -- would leave the answer's grade above the coerced handler's.

    subV-handle : ∀ {A A₁ B B₁ ε ε' ε₁'}
                → (p : A <:ᵛ A₁) → (pε : ε ≾ₑ ε)
                → (q : B₁ <:ᵛ B) → (s : ε₁' ≾ₑ ε')
                → (M : Γ ⊢C⦂ A ! ε)
                → (V : Γ ⊢V⦂ (A₁ ! ε) ⇛ (B₁ ! ε₁'))
                ----------------------------------------------------------------
                → Γ ⊢C⦂ handle M `with subV V ((p !ₛ pε) ⇛ₛ (q !ₛ s))
                     ≡ᵗʰ subC (handle (subC M (p !ₛ pε)) `with V)
                              (q !ₛ ·ₑ-monoʳ-≾ₑ s)

    -- equations for collapsing successive delays

    delay-zero : ∀ {A ε}
               → (M : Γ ⟨ ιᵣ 0ᴰ ⟩ ⊢C⦂ A ! ε)
               --------------------------
               → Γ ⊢C⦂ delay 0ᴰ M
                   ≡ᵗʰ ε-≃ (≃ₑ-sym (≃ₑ-trans (·ₑ-cong ιₑ-zero ≃ₑ-refl) (·ₑ-identityˡ ε)))
                        (C-rename
                          (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ ιᵣ-zero) ∘ʳ ⟨⟩-η-ren)
                          M)

    delay-delay : ∀ {A τ₁ τ₂ ε}
                → (M : Γ ⟨ ιᵣ (τ₁ +ᴰ τ₂) ⟩ ⊢C⦂ A ! ε)
                ------------------------------------
                → Γ ⊢C⦂ delay τ₁ (delay τ₂
                           (C-rename
                             (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ ιᵣ-plus) ∘ʳ ⟨⟩-μ-ren)
                             M))
                    ≡ᵗʰ ε-≃ (≃ₑ-trans (·ₑ-cong ιₑ-plus ≃ₑ-refl) (·ₑ-assoc (ιₑ τ₁) (ιₑ τ₂) ε))
                         (delay (τ₁ +ᴰ τ₂) M)

  infix 18 _⊢C⦂_≡ᵗʰ_
