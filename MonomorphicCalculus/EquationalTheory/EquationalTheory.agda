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

  data _⊢ᵛ⦂_≡ᵗʰ_ (Γ : Ctx) : {A : VType} → Γ ⊢ᵛ⦂ A → Γ ⊢ᵛ⦂ A → Set where

    -- reflexivity, symmetry, transitivity

    V-refl : ∀ {A}
           → {V : Γ ⊢ᵛ⦂ A}
           ---------------
           → Γ ⊢ᵛ⦂ V ≡ᵗʰ V

    V-sym : ∀ {A}
          → {V W : Γ ⊢ᵛ⦂ A}
          → Γ ⊢ᵛ⦂ V ≡ᵗʰ W
          -----------------
          → Γ ⊢ᵛ⦂ W ≡ᵗʰ V

    V-trans : ∀ {A}
            → {V W U : Γ ⊢ᵛ⦂ A}
            → Γ ⊢ᵛ⦂ V ≡ᵗʰ W
            → Γ ⊢ᵛ⦂ W ≡ᵗʰ U
            -------------------
            → Γ ⊢ᵛ⦂ V ≡ᵗʰ U

    -- substitutivity

    V-subst : ∀ {Γ' Γ₁ Γ₂ A B}
            → {V W : Γ' ⊢ᵛ⦂ B}
            → (p : Γ' ⊢ᵛ⦂ V ≡ᵗʰ W)
            → (s : Γ₁ ∷ A , Γ₂ split Γ')
            → (q : Γ₁ ++ᶜ Γ₂ ≡ Γ)
            → (U : Γ₁ ⊢ᵛ⦂ A)
            ---------------------------------------------------------------
            → Γ ⊢ᵛ⦂ subst (_⊢ᵛ⦂ B) q (V [ s ↦ U ]v)
                ≡ᵗʰ subst (_⊢ᵛ⦂ B) q (W [ s ↦ U ]v)

    -- congruence equations

    ⦉⦊-cong : ∀ {A B}
           → {V V' : Γ ⊢ᵛ⦂ A}
           → {W W' : Γ ⊢ᵛ⦂ B}
           → Γ ⊢ᵛ⦂ V ≡ᵗʰ V'
           → Γ ⊢ᵛ⦂ W ≡ᵗʰ W'
           ------------------------------
           → Γ ⊢ᵛ⦂ ⦉ V , W ⦊ ≡ᵗʰ ⦉ V' , W' ⦊

    succ-cong : {V V' : Γ ⊢ᵛ⦂ nat}
              → Γ ⊢ᵛ⦂ V ≡ᵗʰ V'
              ---------------------------
              → Γ ⊢ᵛ⦂ succ V ≡ᵗʰ succ V'

    inl-cong : ∀ {A B}
             → {V V' : Γ ⊢ᵛ⦂ A}
             → Γ ⊢ᵛ⦂ V ≡ᵗʰ V'
             --------------------------------------
             → Γ ⊢ᵛ⦂ inl {B = B} V ≡ᵗʰ inl {B = B} V'

    inr-cong : ∀ {A B}
             → {V V' : Γ ⊢ᵛ⦂ B}
             → Γ ⊢ᵛ⦂ V ≡ᵗʰ V'
             --------------------------------------
             → Γ ⊢ᵛ⦂ inr {A = A} V ≡ᵗʰ inr {A = A} V'

    cons-cong : ∀ {A}
              → {V V' : Γ ⊢ᵛ⦂ A}
              → {W W' : Γ ⊢ᵛ⦂ list A}
              → Γ ⊢ᵛ⦂ V ≡ᵗʰ V'
              → Γ ⊢ᵛ⦂ W ≡ᵗʰ W'
              ---------------------------------
              → Γ ⊢ᵛ⦂ cons V W ≡ᵗʰ cons V' W'

    cmp-cong : ∀ {A ⋈}
             → {V V' W W' : Γ ⊢ᵛ⦂ A}
             → {et : Et A}
             → Γ ⊢ᵛ⦂ V ≡ᵗʰ V'
             → Γ ⊢ᵛ⦂ W ≡ᵗʰ W'
             ------------------------------------------
             → Γ ⊢ᵛ⦂ cmp ⋈ V W et ≡ᵗʰ cmp ⋈ V' W' et

    fun-cong : ∀ {A B ε}
             → {M N : Γ ∷ A ⊢ᶜ⦂ B ! ε}
             → Γ ∷ A ⊢ᶜ⦂ M ≡ᵗʰ N
             -------------------------
             → Γ ⊢ᵛ⦂ fun M ≡ᵗʰ fun N

    handler-cong : ∀ {A B ε ε'}
                 → {N N' : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'}
                 → {H H' : ((op : Op) → (ε'' : E) →
                              Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                                  ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                              ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε''))}
                 → Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ N ≡ᵗʰ N'
                 → ((op : Op) → (ε'' : E) →
                      Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                          ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                      ⊢ᶜ⦂ H op ε'' ≡ᵗʰ H' op ε'')
                 ---------------------------------------------------
                 → Γ ⊢ᵛ⦂ handler N H ≡ᵗʰ handler N' H'

    -- eta equations

    unit-eta : (V : Γ ⊢ᵛ⦂ unit)
             ------------------
             → Γ ⊢ᵛ⦂ V ≡ᵗʰ ⋆

    fun-eta : ∀ {A C}
            → (V : Γ ⊢ᵛ⦂ A ⇒ C)
            -----------------------------------------------
            → Γ ⊢ᵛ⦂ V
                ≡ᵗʰ fun (V-rename wk-ren V · var Hd (≾ᵘ-ok ≾ᵣ-refl))

    -- beta-equation for comparison: at data, the boolean constant of the
    -- relation's truth on their order

    cmp-beta : ∀ {A}
             → (⋈ : Cmp)
             → (et : Et A)
             → (d e : ⟪ A ⟫)
             -------------------------------------------------------------
             → Γ ⊢ᵛ⦂ cmp ⋈ (⌈ et ⌉ d) (⌈ et ⌉ e) et
                 ≡ᵗʰ ⌈ holds ⋈ (compareᵈ et d e) ⌉ᵇ

    -- equations for subsumption
    --
    -- Subsumption is erased, so it obeys exactly the laws of the coercion it
    -- denotes: witness irrelevance, and functoriality in the witness.

    subV-cong : ∀ {A A'}
              → {w w' : A <:ᵛ A'}
              → {V W : Γ ⊢ᵛ⦂ A}
              → Γ ⊢ᵛ⦂ V ≡ᵗʰ W
              ------------------------------
              → Γ ⊢ᵛ⦂ subV V w ≡ᵗʰ subV W w'

    subV-refl : ∀ {A}
              → (w : A <:ᵛ A)
              → (V : Γ ⊢ᵛ⦂ A)
              ----------------------
              → Γ ⊢ᵛ⦂ subV V w ≡ᵗʰ V

    subV-trans : ∀ {A₁ A₂ A₃}
               → (w : A₁ <:ᵛ A₂) → (w' : A₂ <:ᵛ A₃) → (w'' : A₁ <:ᵛ A₃)
               → (V : Γ ⊢ᵛ⦂ A₁)
               ------------------------------------------
               → Γ ⊢ᵛ⦂ subV (subV V w) w' ≡ᵗʰ subV V w''

    -- Subsumption is natural in the value formers: the witness splits the way
    -- its type does. At `⦉_,_⦊` that is functoriality of `_|×|_`, at `inl` and
    -- `inr` functoriality of `_|+|_`, at `nil` and `cons` functoriality of
    -- `list`, at `fun` functoriality of `_⇒_`, contravariant in the domain,
    -- so the binder is subsumed rather than the body coerced there. The atomic formers and `var` have no rule of their
    -- own.

    subV-pair : ∀ {A A' B B'}
              → (p : A <:ᵛ A') → (q : B <:ᵛ B')
              → (V : Γ ⊢ᵛ⦂ A)
              → (W : Γ ⊢ᵛ⦂ B)
              ------------------------------------------------------
              → Γ ⊢ᵛ⦂ subV ⦉ V , W ⦊ (p |×|ₛ q)
                   ≡ᵗʰ ⦉ subV V p , subV W q ⦊

    subV-inl : ∀ {A A' B B'}
             → (p : A <:ᵛ A') → (q : B <:ᵛ B')
             → (V : Γ ⊢ᵛ⦂ A)
             ---------------------------------------------------
             → Γ ⊢ᵛ⦂ subV (inl V) (p |+|ₛ q) ≡ᵗʰ inl (subV V p)

    subV-inr : ∀ {A A' B B'}
             → (p : A <:ᵛ A') → (q : B <:ᵛ B')
             → (V : Γ ⊢ᵛ⦂ B)
             ---------------------------------------------------
             → Γ ⊢ᵛ⦂ subV (inr V) (p |+|ₛ q) ≡ᵗʰ inr (subV V q)

    subV-nil : ∀ {A A'}
             → (p : A <:ᵛ A')
             ---------------------------------------------
             → Γ ⊢ᵛ⦂ subV (nil {A = A}) (listₛ p) ≡ᵗʰ nil

    subV-cons : ∀ {A A'}
              → (p : A <:ᵛ A')
              → (V : Γ ⊢ᵛ⦂ A)
              → (W : Γ ⊢ᵛ⦂ list A)
              ------------------------------------------------------------
              → Γ ⊢ᵛ⦂ subV (cons V W) (listₛ p)
                   ≡ᵗʰ cons (subV V p) (subV W (listₛ p))

    subV-fun : ∀ {A A' C C'}
             → (p : A' <:ᵛ A)
             → (w : C <:ᶜ C')
             → (M : Γ ∷ A ⊢ᶜ⦂ C)
             ------------------------------------------------------
             → Γ ⊢ᵛ⦂ subV (fun M) (p ⇒ₛ w)
                  ≡ᵗʰ fun (subC (subCtx p M) w)

  infix 18 _⊢ᵛ⦂_≡ᵗʰ_

  -- computation equations

  data _⊢ᶜ⦂_≡ᵗʰ_ (Γ : Ctx) : {C : CType} → Γ ⊢ᶜ⦂ C → Γ ⊢ᶜ⦂ C → Set where

    -- reflexivity, symmetry, transitivity

    C-refl : ∀ {C}
           → {M : Γ ⊢ᶜ⦂ C}
           ---------------
           → Γ ⊢ᶜ⦂ M ≡ᵗʰ M

    C-sym : ∀ {C}
          → {M N : Γ ⊢ᶜ⦂ C}
          → Γ ⊢ᶜ⦂ M ≡ᵗʰ N
          -----------------
          → Γ ⊢ᶜ⦂ N ≡ᵗʰ M

    C-trans : ∀ {C}
            → {M N P : Γ ⊢ᶜ⦂ C}
            → Γ ⊢ᶜ⦂ M ≡ᵗʰ N
            → Γ ⊢ᶜ⦂ N ≡ᵗʰ P
            -------------------
            → Γ ⊢ᶜ⦂ M ≡ᵗʰ P

    -- substitutivity

    C-subst : ∀ {Γ' Γ₁ Γ₂ A C}
            → {M N : Γ' ⊢ᶜ⦂ C}
            → (p : Γ' ⊢ᶜ⦂ M ≡ᵗʰ N)
            → (s : Γ₁ ∷ A , Γ₂ split Γ')
            → (q : Γ₁ ++ᶜ Γ₂ ≡ Γ)
            → (V : Γ₁ ⊢ᵛ⦂ A)
            ---------------------------------------------------------------
            → Γ ⊢ᶜ⦂ subst (_⊢ᶜ⦂ C) q (M [ s ↦ V ]c)
                ≡ᵗʰ subst (_⊢ᶜ⦂ C) q (N [ s ↦ V ]c)

    -- congruence equations

    return-cong : ∀ {A}
                → {V W : Γ ⊢ᵛ⦂ A}
                → Γ ⊢ᵛ⦂ V ≡ᵗʰ W
                ----------------------------
                → Γ ⊢ᶜ⦂ return V ≡ᵗʰ return W

    seq-cong : ∀ {A B ε ε'}
             → {M M' : Γ ⊢ᶜ⦂ A ! ε}
             → {N N' : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'}
             → Γ ⊢ᶜ⦂ M ≡ᵗʰ M'
             → Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ N ≡ᵗʰ N'
             ---------------------------------
             → Γ ⊢ᶜ⦂ M ⨟ N ≡ᵗʰ M' ⨟ N'

    app-cong : ∀ {A C}
             → {V V' : Γ ⊢ᵛ⦂ A ⇒ C}
             → {W W' : Γ ⊢ᵛ⦂ A}
             → Γ ⊢ᵛ⦂ V ≡ᵗʰ V'
             → Γ ⊢ᵛ⦂ W ≡ᵗʰ W'
             ------------------------
             → Γ ⊢ᶜ⦂ V · W ≡ᵗʰ V' · W'

    match-cong : ∀ {A B C}
               → {V W : Γ ⊢ᵛ⦂ A |×| B}
               → {M N : Γ ∷ A ∷ B ⊢ᶜ⦂ C}
               → Γ ⊢ᵛ⦂ V ≡ᵗʰ W
               → Γ ∷ A ∷ B ⊢ᶜ⦂ M ≡ᵗʰ N
               --------------------------------------
               → Γ ⊢ᶜ⦂ match V `with M ≡ᵗʰ match W `with N

    absurd-cong : ∀ {C}
                → {V W : Γ ⊢ᵛ⦂ empty}
                → Γ ⊢ᵛ⦂ V ≡ᵗʰ W
                ------------------------------------
                → Γ ⊢ᶜ⦂ absurd {C = C} V ≡ᵗʰ absurd {C = C} W

    if-cong : ∀ {C}
            → {V W : Γ ⊢ᵛ⦂ bool}
            → {M M' N N' : Γ ⊢ᶜ⦂ C}
            → Γ ⊢ᵛ⦂ V ≡ᵗʰ W
            → Γ ⊢ᶜ⦂ M ≡ᵗʰ M'
            → Γ ⊢ᶜ⦂ N ≡ᵗʰ N'
            ----------------------------------------------------------
            → Γ ⊢ᶜ⦂ if V `then M `else N ≡ᵗʰ if W `then M' `else N'

    matchℕ-cong : ∀ {C}
                → {V W : Γ ⊢ᵛ⦂ nat}
                → {M M' : Γ ⊢ᶜ⦂ C}
                → {N N' : Γ ∷ nat ⊢ᶜ⦂ C}
                → Γ ⊢ᵛ⦂ V ≡ᵗʰ W
                → Γ ⊢ᶜ⦂ M ≡ᵗʰ M'
                → Γ ∷ nat ⊢ᶜ⦂ N ≡ᵗʰ N'
                --------------------------------------------------------------
                → Γ ⊢ᶜ⦂ matchℕ V `zero M `succ N ≡ᵗʰ matchℕ W `zero M' `succ N'

    recℕ-cong : ∀ {B ε}
              → {V W : Γ ⊢ᵛ⦂ nat}
              → {M M' : Γ ⊢ᶜ⦂ B ! ε}
              → {N N' : (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
              → {p : ε ·ₑ ε ≾ₑ ε}
              → Γ ⊢ᵛ⦂ V ≡ᵗʰ W
              → Γ ⊢ᶜ⦂ M ≡ᵗʰ M'
              → (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ N ≡ᵗʰ N'
              -----------------------------------------------
              → Γ ⊢ᶜ⦂ recℕ V M N p ≡ᵗʰ recℕ W M' N' p

    matchL-cong : ∀ {A C}
                → {V W : Γ ⊢ᵛ⦂ list A}
                → {M M' : Γ ⊢ᶜ⦂ C}
                → {N N' : Γ ∷ A ∷ list A ⊢ᶜ⦂ C}
                → Γ ⊢ᵛ⦂ V ≡ᵗʰ W
                → Γ ⊢ᶜ⦂ M ≡ᵗʰ M'
                → Γ ∷ A ∷ list A ⊢ᶜ⦂ N ≡ᵗʰ N'
                ------------------------------------------------------------
                → Γ ⊢ᶜ⦂ matchL V `nil M `cons N ≡ᵗʰ matchL W `nil M' `cons N'

    recL-cong : ∀ {A B ε}
              → {V W : Γ ⊢ᵛ⦂ list A}
              → {M M' : Γ ⊢ᶜ⦂ B ! ε}
              → {N N' : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
              → {p : ε ·ₑ ε ≾ₑ ε}
              → Γ ⊢ᵛ⦂ V ≡ᵗʰ W
              → Γ ⊢ᶜ⦂ M ≡ᵗʰ M'
              → (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ N ≡ᵗʰ N'
              ---------------------------------------------------------
              → Γ ⊢ᶜ⦂ recL V M N p ≡ᵗʰ recL W M' N' p

    match+-cong : ∀ {A B C}
                → {V W : Γ ⊢ᵛ⦂ A |+| B}
                → {M M' : Γ ∷ A ⊢ᶜ⦂ C}
                → {N N' : Γ ∷ B ⊢ᶜ⦂ C}
                → Γ ⊢ᵛ⦂ V ≡ᵗʰ W
                → Γ ∷ A ⊢ᶜ⦂ M ≡ᵗʰ M'
                → Γ ∷ B ⊢ᶜ⦂ N ≡ᵗʰ N'
                ------------------------------------------------------------
                → Γ ⊢ᶜ⦂ match+ V `inl M `inr N ≡ᵗʰ match+ W `inl M' `inr N'

    perform-cong : ∀ {A ε op}
                 → {V W : Γ ⊢ᵛ⦂ ⌜ param op ⌝ᵍ}
                 → {M N : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ A ! ε}
                 → Γ ⊢ᵛ⦂ V ≡ᵗʰ W
                 → Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ M ≡ᵗʰ N
                 ---------------------------------------------------------------
                 → Γ ⊢ᶜ⦂ perform op V M ≡ᵗʰ perform op W N

    delay-cong  : ∀ {A τ ε}
                → {M N : Γ ⟨ ιᵣ τ ⟩ ⊢ᶜ⦂ A ! ε}
                → Γ ⟨ ιᵣ τ ⟩ ⊢ᶜ⦂ M ≡ᵗʰ N
                --------------------------------------
                → Γ ⊢ᶜ⦂ delay τ M ≡ᵗʰ delay τ N

    handle-cong : ∀ {A B ε ε'}
                → {M M' : Γ ⊢ᶜ⦂ A ! ε}
                → {V V' : Γ ⊢ᵛ⦂ (A ! ε) ⇛ (B ! ε')}
                → Γ ⊢ᶜ⦂ M ≡ᵗʰ M'
                → Γ ⊢ᵛ⦂ V ≡ᵗʰ V'
                -----------------------------------------------
                → Γ ⊢ᶜ⦂ handle M `with V ≡ᵗʰ handle M' `with V'

    -- The grade bound and the payload subsumption an `unbox` stores are both
    -- irrelevant, so the two nodes are compared at the resource variable they
    -- name.

    unbox-cong : ∀ {A A₀ C ρ₀ ρ'}
               → {x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ}
               → {rel rel' : ρ' ≾ᵣ ρ₀}
               → {w w' : A₀ <:ᵛ A}
               → {M N : Γ ∷ A  ⊢ᶜ⦂ C}
               → Γ ∷ A ⊢ᶜ⦂ M ≡ᵗʰ N
               ------------------------------------------------
               → Γ ⊢ᶜ⦂ unbox x rel w M ≡ᵗʰ unbox x rel' w' N

    box-cong : ∀ {A C ρ}
             → {V W : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A}
             → {M N : Γ ∷ [ ρ ] A ⊢ᶜ⦂ C}
             → Γ ⟨ ρ ⟩ ⊢ᵛ⦂ V ≡ᵗʰ W
             → Γ ∷ [ ρ ] A ⊢ᶜ⦂ M ≡ᵗʰ N
             --------------------------
             → Γ ⊢ᶜ⦂ box _ V M ≡ᵗʰ box _ W N

    subC-cong : ∀ {C C'}
              → {w w' : C <:ᶜ C'}
              → {M N : Γ ⊢ᶜ⦂ C}
              → Γ ⊢ᶜ⦂ M ≡ᵗʰ N
              ------------------------------
              → Γ ⊢ᶜ⦂ subC M w ≡ᵗʰ subC N w'

    -- computational/beta-equations for sequential composition

    seq-return : ∀ {A B ε}
               → (V : Γ ⊢ᵛ⦂ A)
               → (M : Γ ⟨ ∣ 𝟏ₑ ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε)
               -----------------------------------------------------
               → Γ ⊢ᶜ⦂ return V ⨟ M
                   ≡ᵗʰ ε-≃ (≃ₑ-sym (·ₑ-identityˡ ε))
                        ((C-rename
                           (cong-∷-ren
                             (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-𝟏ᵉ) ∘ʳ ⟨⟩-η-ren))
                           M)
                         [ V ]₀)

    seq-perform : ∀ {A B ε ε' op}
                → (V : Γ ⊢ᵛ⦂ ⌜ param op ⌝ᵍ)
                → (M : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ A ! ε)
                → (N : Γ ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε')
                ---------------------------------------------------------------------
                → Γ ⊢ᶜ⦂ (perform op V M) ⨟ N
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
              → (M : Γ ⟨ ιᵣ τ ⟩ ⊢ᶜ⦂ A ! ε)
              → (N : Γ ⟨ ∣ ιₑ τ ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε')
              -------------------------------------------------------
              → Γ ⊢ᶜ⦂ delay τ M ⨟ N
                  ≡ᵗʰ ε-≃ (≃ₑ-sym (·ₑ-assoc (ιₑ τ) ε ε'))
                       (delay τ
                         (M ⨟
                          C-rename
                            (cong-∷-ren
                              (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ (≃ᵣ-trans map-·ᵉ (·ᵣ-cong map-ιᵉ ≃ᵣ-refl)))
                               ∘ʳ ⟨⟩-μ-ren))
                            N))

    seq-box : ∀ {A B C ρ ε ε'}
            → (V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A)
            → (M : Γ ∷ [ ρ ] A ⊢ᶜ⦂ B ! ε)
            → (N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ C ! ε')
            -------------------------------------------------------
            → Γ ⊢ᶜ⦂ box _ V M ⨟ N
                ≡ᵗʰ box _ V (M ⨟ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N)

    seq-unbox : ∀ {A A₀ B C ρ₀ ρ' ε ε'}
              → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
              → (rel : ρ' ≾ᵣ ρ₀)
              → (w : A₀ <:ᵛ A)
              → (M : Γ ∷ A ⊢ᶜ⦂ B ! ε)
              → (N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ C ! ε')
              -------------------------------------------------------
              → Γ ⊢ᶜ⦂ unbox x rel w M ⨟ N
                  ≡ᵗʰ unbox x rel w (M ⨟ C-rename (cong-∷-ren (cong-⟨⟩-ren wk-ren)) N)

    -- eta-equation for sequential composition

    seq-eta : ∀ {A ε}
            → (M : Γ ⊢ᶜ⦂ A ! ε)
            ----------------------------------------------------------
            → Γ ⊢ᶜ⦂ M
                ≡ᵗʰ ε-≃ (·ₑ-identityʳ ε) (M ⨟ return (var Hd (≾ᵘ-ok ≾ᵣ-refl)))

    -- associativity equation for sequential composition

    seq-assoc : ∀ {A B C ε ε' ε''}
              → (M : Γ ⊢ᶜ⦂ A ! ε)
              → (N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε')
              → (P : Γ ⟨ ∣ ε ·ₑ ε' ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ C ! ε'')
              ---------------------------------------------------------------------
              → Γ ⊢ᶜ⦂ (M ⨟ N) ⨟ P
                  ≡ᵗʰ ε-≃ (≃ₑ-sym (·ₑ-assoc ε ε' ε''))
                       (M ⨟ (N ⨟ C-rename
                                   (cong-∷-ren
                                     ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ)
                                      ∘ʳ ⟨⟩-μ-ren)
                                      ∘ʳ cong-⟨⟩-ren wk-ren))
                                   P))

    -- computational/beta-equation for function application

    fun-beta : ∀ {A C}
             → (M : Γ ∷ A ⊢ᶜ⦂ C)
             → (W : Γ ⊢ᵛ⦂ A)
             ----------------------
             → Γ ⊢ᶜ⦂ fun M · W
                 ≡ᵗʰ M [ W ]₀

    -- beta-equation for pattern-matching

    match-beta : ∀ {A B C}
               → (V : Γ ⊢ᵛ⦂ A)
               → (W : Γ ⊢ᵛ⦂ B)
               → (M : Γ ∷ A ∷ B ⊢ᶜ⦂ C)
               ------------------------------------
               → Γ ⊢ᶜ⦂ match ⦉ V , W ⦊ `with M
                   ≡ᵗʰ M [ V-rename wk-ren W ]₀
                         [ V ]₀

    -- eta-equation for pattern-matching

    match-eta : ∀ {A B C}
              → (V : Γ ⊢ᵛ⦂ A |×| B)
              → (M : Γ ∷ A |×| B ⊢ᶜ⦂ C)
              -------------------------------------------------------------
              → Γ ⊢ᶜ⦂ match V `with
                       ((C-rename (wk-ren ∘ʳ exch-ren ∘ʳ wk-ren ∘ʳ exch-ren)
                         M) [ ⦉ var (Tl-∷ Hd) (≾ᵘ-ok ≾ᵣ-refl) , var Hd (≾ᵘ-ok ≾ᵣ-refl) ⦊ ]₀)
                  ≡ᵗʰ M [ V ]₀

    -- eta-equation for empty type elimination

    absurd-eta : ∀ {C}
               → (V : Γ ⊢ᵛ⦂ empty)
               → (M : Γ ∷ empty ⊢ᶜ⦂ C)
               -----------------------
               → Γ ⊢ᶜ⦂ absurd {C = C} V
                   ≡ᵗʰ M [ V ]₀

    -- beta-equations for boolean elimination

    if-beta-true : ∀ {C}
                 → (M N : Γ ⊢ᶜ⦂ C)
                 -----------------------------------------
                 → Γ ⊢ᶜ⦂ if true `then M `else N ≡ᵗʰ M

    if-beta-false : ∀ {C}
                  → (M N : Γ ⊢ᶜ⦂ C)
                  -----------------------------------------
                  → Γ ⊢ᶜ⦂ if false `then M `else N ≡ᵗʰ N

    -- eta-equation for boolean elimination
    --
    -- Commuting conversions are instances of this rule.

    if-eta : ∀ {C}
           → (V : Γ ⊢ᵛ⦂ bool)
           → (M : Γ ∷ bool ⊢ᶜ⦂ C)
           ------------------------------------------------------
           → Γ ⊢ᶜ⦂ if V `then (M [ true  ]₀)
                        `else (M [ false ]₀)
               ≡ᵗʰ M [ V ]₀

    -- beta-equations for natural-number elimination

    matchℕ-beta-zero : ∀ {C}
                     → (M : Γ ⊢ᶜ⦂ C)
                     → (N : Γ ∷ nat ⊢ᶜ⦂ C)
                     -------------------------------------------
                     → Γ ⊢ᶜ⦂ matchℕ zero `zero M `succ N ≡ᵗʰ M

    matchℕ-beta-succ : ∀ {C}
                     → (V : Γ ⊢ᵛ⦂ nat)
                     → (M : Γ ⊢ᶜ⦂ C)
                     → (N : Γ ∷ nat ⊢ᶜ⦂ C)
                     -------------------------------------------------------------
                     → Γ ⊢ᶜ⦂ matchℕ succ V `zero M `succ N ≡ᵗʰ N [ V ]₀

    -- eta-equation for natural-number elimination
    --
    -- Commuting conversions are instances of this rule.

    matchℕ-eta : ∀ {C}
               → (V : Γ ⊢ᵛ⦂ nat)
               → (M : Γ ∷ nat ⊢ᶜ⦂ C)
               ------------------------------------------------------------------
               → Γ ⊢ᶜ⦂ matchℕ V
                        `zero (M [ zero ]₀)
                        `succ (C-rename (cong-∷-ren wk-ren) M
                                [ succ (var Hd (≾ᵘ-ok ≾ᵣ-refl)) ]₀)
                   ≡ᵗʰ M [ V ]₀

    -- beta-equations for primitive recursion
    --
    -- There is no eta-equation: the recursor's uniqueness is an induction
    -- principle over the scrutinee, not an equation between two terms.

    recℕ-beta-zero : ∀ {B ε}
                   → (M : Γ ⊢ᶜ⦂ B ! ε)
                   → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε)
                   → (p : ε ·ₑ ε ≾ₑ ε)
                   ---------------------------------------
                   → Γ ⊢ᶜ⦂ recℕ zero M N p ≡ᵗʰ M

    recℕ-beta-succ : ∀ {B ε}
                   → (V : Γ ⊢ᵛ⦂ nat)
                   → (M : Γ ⊢ᶜ⦂ B ! ε)
                   → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε)
                   → (p : ε ·ₑ ε ≾ₑ ε)
                   ------------------------------------------------------------
                   → Γ ⊢ᶜ⦂ recℕ (succ V) M N p
                       ≡ᵗʰ coerce p (recℕ V M N p ⨟ recℕ-step V N)

    -- beta-equations for sum elimination

    match+-beta-inl : ∀ {A B C}
                    → (V : Γ ⊢ᵛ⦂ A)
                    → (M : Γ ∷ A ⊢ᶜ⦂ C)
                    → (N : Γ ∷ B ⊢ᶜ⦂ C)
                    ----------------------------------------------------------
                    → Γ ⊢ᶜ⦂ match+ inl V `inl M `inr N ≡ᵗʰ M [ V ]₀

    match+-beta-inr : ∀ {A B C}
                    → (V : Γ ⊢ᵛ⦂ B)
                    → (M : Γ ∷ A ⊢ᶜ⦂ C)
                    → (N : Γ ∷ B ⊢ᶜ⦂ C)
                    ----------------------------------------------------------
                    → Γ ⊢ᶜ⦂ match+ inr V `inl M `inr N ≡ᵗʰ N [ V ]₀

    -- eta-equation for sum elimination
    --
    -- Commuting conversions are instances of this rule.

    match+-eta : ∀ {A B C}
               → (V : Γ ⊢ᵛ⦂ A |+| B)
               → (M : Γ ∷ A |+| B ⊢ᶜ⦂ C)
               ------------------------------------------------------------------
               → Γ ⊢ᶜ⦂ match+ V
                        `inl (C-rename (cong-∷-ren wk-ren) M
                                [ inl (var Hd (≾ᵘ-ok ≾ᵣ-refl)) ]₀)
                        `inr (C-rename (cong-∷-ren wk-ren) M
                                [ inr (var Hd (≾ᵘ-ok ≾ᵣ-refl)) ]₀)
                   ≡ᵗʰ M [ V ]₀

    -- beta-equations for list elimination

    matchL-beta-nil : ∀ {A C}
                    → (M : Γ ⊢ᶜ⦂ C)
                    → (N : Γ ∷ A ∷ list A ⊢ᶜ⦂ C)
                    -----------------------------------------
                    → Γ ⊢ᶜ⦂ matchL nil `nil M `cons N ≡ᵗʰ M

    matchL-beta-cons : ∀ {A C}
                     → (V : Γ ⊢ᵛ⦂ A)
                     → (W : Γ ⊢ᵛ⦂ list A)
                     → (M : Γ ⊢ᶜ⦂ C)
                     → (N : Γ ∷ A ∷ list A ⊢ᶜ⦂ C)
                     ----------------------------------------------
                     → Γ ⊢ᶜ⦂ matchL cons V W `nil M `cons N
                         ≡ᵗʰ N [ V-rename wk-ren W ]₀
                               [ V ]₀

    -- eta-equation for list elimination
    --
    -- Commuting conversions are instances of this rule.

    matchL-eta : ∀ {A C}
               → (V : Γ ⊢ᵛ⦂ list A)
               → (M : Γ ∷ list A ⊢ᶜ⦂ C)
               -------------------------------------------------------------
               → Γ ⊢ᶜ⦂ matchL V
                        `nil (M [ nil ]₀)
                        `cons ((C-rename (wk-ren ∘ʳ exch-ren ∘ʳ wk-ren ∘ʳ exch-ren) M)
                                 [ cons (var (Tl-∷ Hd) (≾ᵘ-ok ≾ᵣ-refl))
                                                   (var Hd (≾ᵘ-ok ≾ᵣ-refl)) ]₀)
                   ≡ᵗʰ M [ V ]₀

    -- beta-equations for primitive recursion on lists; no eta-equation, as
    -- for `recℕ`

    recL-beta-nil : ∀ {A B ε}
                  → (M : Γ ⊢ᶜ⦂ B ! ε)
                  → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε)
                  → (p : ε ·ₑ ε ≾ₑ ε)
                  ---------------------------------------
                  → Γ ⊢ᶜ⦂ recL nil M N p ≡ᵗʰ M

    recL-beta-cons : ∀ {A B ε}
                   → (V : Γ ⊢ᵛ⦂ A)
                   → (W : Γ ⊢ᵛ⦂ list A)
                   → (M : Γ ⊢ᶜ⦂ B ! ε)
                   → (N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε)
                   → (p : ε ·ₑ ε ≾ₑ ε)
                   ------------------------------------------------------------
                   → Γ ⊢ᶜ⦂ recL (cons V W) M N p
                       ≡ᵗʰ coerce p (recL W M N p ⨟ recL-step V W N)

    -- computational/beta-equations for effect handling
    --
    -- `return`, `perform` and `delay` are handled by a handler literal, whose
    -- clause family is re-barred across the binder or lock the handle moves
    -- under. The binders `box` and `unbox` commute with handling by any
    -- handler value, weakened past them. Handler values have no η-law.

    handle-return : ∀ {A B ε}
                  → (V : Γ ⊢ᵛ⦂ A)
                  → (H : (op : Op) → (ε'' : E) →
                           Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                               ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                           ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε''))
                  → (N : Γ ⟨ ∣ 𝟏ₑ ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε)
                  ----------------------------------------------------------------
                  → Γ ⊢ᶜ⦂ handle return V `with handler N H
                      ≡ᵗʰ ε-≃ (≃ₑ-sym (·ₑ-identityˡ ε))
                           ((C-rename
                              (cong-∷-ren
                                (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-𝟏ᵉ) ∘ʳ ⟨⟩-η-ren))
                              N)
                            [ V ]₀)

    handle-perform : ∀ {A B ε ε' op}
                   → (V : Γ ⊢ᵛ⦂ ⌜ param op ⌝ᵍ)
                   → (M : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ A ! ε)
                   → (H : (op : Op) → (ε'' : E) →
                            Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                                ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                            ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε''))
                   → (N : Γ ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε')
                   ----------------------------------------------------------------
                   → Γ ⊢ᶜ⦂ handle perform op V M `with handler N H
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
                                   [ V ]₁))

    handle-delay : ∀ {A B τ ε ε'}
                 → (M : Γ ⟨ ιᵣ τ ⟩ ⊢ᶜ⦂ A ! ε)
                 → (H : (op : Op) → (ε'' : E) →
                          Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                              ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                          ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε''))
                 → (N : Γ ⟨ ∣ ιₑ τ ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε')
                 ------------------------------------------------------------------------------
                 → Γ ⊢ᶜ⦂ handle delay τ M `with handler N H
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
               → (V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A)
               → (M : Γ ∷ [ ρ ] A ⊢ᶜ⦂ B ! ε)
               → (W : Γ ⊢ᵛ⦂ (B ! ε) ⇛ (C ! ε'))
               ------------------------------------------------------------
               → Γ ⊢ᶜ⦂ handle box _ V M `with W
                   ≡ᵗʰ box _ V (handle M `with V-rename wk-ren W)

    handle-unbox : ∀ {A A₀ B C ρ₀ ρ' ε ε'}
                 → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
                 → (rel : ρ' ≾ᵣ ρ₀)
                 → (w : A₀ <:ᵛ A)
                 → (M : Γ ∷ A ⊢ᶜ⦂ B ! ε)
                 → (V : Γ ⊢ᵛ⦂ (B ! ε) ⇛ (C ! ε'))
                 ------------------------------------------------------------
                 → Γ ⊢ᶜ⦂ handle unbox x rel w M `with V
                     ≡ᵗʰ unbox x rel w (handle M `with V-rename wk-ren V)

    -- beta rule for unbox

    unbox-beta : ∀ {A A' C D ρ}
               → (V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A)
               → (K : Γ ∷ [ ρ ] A ⊢K[ all ◁ D ]⦂ C)
               → (p : ctx-grade (hole-ctx K) ≾ᵣ ρ)
               → (w : A <:ᵛ A')
               → (N : (Γ ∷ [ ρ ] A ++ᶜ hole-ctx K) ∷ A' ⊢ᶜ⦂ D)
               -----------------------------------------------------------------------
               → Γ ⊢ᶜ⦂ box _ V (K [ unbox (∈-++ᶜˡ (hole-ctx K) Hd)
                                        (≾ᵣ-trans (≾ᵣ-reflexive
                                                    (grade-++ᶜˡ-𝟏ᵣ (hole-ctx K)))
                                                  p)
                                        w N ])
                   ≡ᵗʰ box _ V (K [ N [ subV (V-rename ((cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-≤-ren p) ∘ʳ wk-ren-⟨ρ⟩-ctx refl) V) w ]₀ ])


    -- unboxing non-related values commute

    unbox-comm : ∀ {A A₁ B B₂ C ρ₁ ρ₁' ρ₂ ρ₂'}
               → (x₁ : [ ρ₁ ] A₁ ∈[ ρ₁' ] Γ)
               → (rel₁ : ρ₁' ≾ᵣ ρ₁)
               → (w₁ : A₁ <:ᵛ A)
               → (x₂ : [ ρ₂ ] B₂ ∈[ ρ₂' ] Γ)
               → (rel₂ : ρ₂' ≾ᵣ ρ₂)
               → (w₂ : B₂ <:ᵛ B)
               → (M : Γ ∷ A ∷ B ⊢ᶜ⦂ C)
               ----------------------------------------------------
               → Γ ⊢ᶜ⦂ unbox x₁ rel₁ w₁
                        (unbox (Tl-∷ x₂) rel₂ w₂ M)
                   ≡ᵗʰ unbox x₂ rel₂ w₂
                        (unbox (Tl-∷ x₁) rel₁ w₁
                               (C-rename exch-ren M))


    -- boxing resources commute

    box-comm : ∀ {A B C ρ ρ'}
             → (V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A)
             → (W : Γ ⟨ ρ' ⟩ ⊢ᵛ⦂ B)
             → (M : Γ ∷ [ ρ ] A ∷ [ ρ' ] B ⊢ᶜ⦂ C)
             -------------------------------------------------
             → Γ ⊢ᶜ⦂ box _ V
                     (box _ (V-rename (cong-⟨⟩-ren wk-ren) W) M)
                 ≡ᵗʰ box _ W
                     (box _
                       (V-rename (cong-⟨⟩-ren wk-ren) V)
                       (C-rename exch-ren M))

    -- eta rule for box
    
    boxed-not-used : ∀ {A C ρ ε}
                   → (V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A)
                   → (M : Γ ⊢ᶜ⦂ C ! ε)
                   -----------------------------------
                   → Γ ⊢ᶜ⦂ box _ V (C-rename wk-ren M)
                       ≡ᵗʰ M

    -- eta rule for unbox

    unbox-not-used : ∀ {A A₀ C ρ₀ ρ'}
                   → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
                   → (rel : ρ' ≾ᵣ ρ₀)
                   → (w : A₀ <:ᵛ A)
                   → (M : Γ ⊢ᶜ⦂ C)
                   ---------------------------------------------------
                   → Γ ⊢ᶜ⦂ unbox x rel w (C-rename (wk-ren {A = A}) M)
                       ≡ᵗʰ M

    -- boxing and unboxing unrelated resources commute

    box-unbox-comm : ∀ {A B B₂ C ρ ρ₂ ρ₂'}
                   → (V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A)
                   → (x₂ : [ ρ₂ ] B₂ ∈[ ρ₂' ] Γ)
                   → (rel₂ : ρ₂' ≾ᵣ ρ₂)
                   → (w₂ : B₂ <:ᵛ B)
                   → (M : Γ ∷ [ ρ ] A ∷ B ⊢ᶜ⦂ C)
                   -----------------------------------
                   → Γ ⊢ᶜ⦂ box _ V
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
              → (M : Γ ⊢ᶜ⦂ C)
              ------------------------
              → Γ ⊢ᶜ⦂ subC M w ≡ᵗʰ M

    subC-trans : ∀ {C₁ C₂ C₃}
               → (w : C₁ <:ᶜ C₂) → (w' : C₂ <:ᶜ C₃) → (w'' : C₁ <:ᶜ C₃)
               → (M : Γ ⊢ᶜ⦂ C₁)
               ----------------------------------------------
               → Γ ⊢ᶜ⦂ subC (subC M w) w' ≡ᵗʰ subC M w''

    subC-perform : ∀ {A A' ε ε' op}
                 → (w : A <:ᵛ A')
                 → (rel : ε ≾ₑ ε')
                 → (V : Γ ⊢ᵛ⦂ ⌜ param op ⌝ᵍ)
                 → (M : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
                        ⊢ᶜ⦂ A ! ε)
                 ----------------------------------------------------------
                 → Γ ⊢ᶜ⦂ subC (perform op V M) (w !ₛ ·ₑ-monoʳ-≾ₑ rel)
                      ≡ᵗʰ perform op V (subC M (w !ₛ rel))

    subC-delay : ∀ {A A' τ ε ε'}
               → (w : A <:ᵛ A')
               → (rel : ε ≾ₑ ε')
               → (M : Γ ⟨ ιᵣ τ ⟩ ⊢ᶜ⦂ A ! ε)
               ------------------------------------------------
               → Γ ⊢ᶜ⦂ subC (delay τ M) (w !ₛ ·ₑ-monoʳ-≾ₑ rel)
                    ≡ᵗʰ delay τ (subC M (w !ₛ rel))

    -- Moving a scrutinee's subsumption outwards relaxes the continuation's
    -- lock along the effect half and subsumes its binder along the value half.
    -- For `handle` both halves move onto the handler value. Neither `_⨟_` nor
    -- `handle_`with_` carries a payload witness of its own, as `unbox` does.

    subC-seq : ∀ {A A' B ε₁ ε₂ ε'}
             → (w : A <:ᵛ A')
             → (rel : ε₁ ≾ₑ ε₂)
             → (M : Γ ⊢ᶜ⦂ A ! ε₁)
             → (N : Γ ⟨ ∣ ε₂ ∣ᵉ ⟩ ∷ A' ⊢ᶜ⦂ B ! ε')
             ------------------------------------------------------------
             → Γ ⊢ᶜ⦂ subC M (w !ₛ rel) ⨟ N
                  ≡ᵗʰ coerce (·ₑ-monoˡ-≾ₑ rel)
                       (M ⨟ subCtx w
                              (C-rename
                                (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ rel))) N))

    subC-handle : ∀ {A A' B ε₁ ε₂ ε'}
                → (w : A <:ᵛ A')
                → (rel : ε₁ ≾ₑ ε₂)
                → (M : Γ ⊢ᶜ⦂ A ! ε₁)
                → (V : Γ ⊢ᵛ⦂ (A' ! ε₂) ⇛ (B ! ε'))
                ----------------------------------------------------------------
                → Γ ⊢ᶜ⦂ handle (subC M (w !ₛ rel)) `with V
                     ≡ᵗʰ coerce (·ₑ-monoˡ-≾ₑ rel)
                          (handle M `with subV V ((w !ₛ rel) ⇛ₛ <:ᶜ-refl (B ! ε')))

    -- `box` and `unbox` bind but compute nothing, so a subsumption of the
    -- node is a subsumption of the body, at an unrestricted witness.

    subC-box : ∀ {A C C' ρ}
             → (w : C <:ᶜ C')
             → (V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A)
             → (M : Γ ∷ [ ρ ] A ⊢ᶜ⦂ C)
             ----------------------------------------------------
             → Γ ⊢ᶜ⦂ subC (box _ V M) w ≡ᵗʰ box _ V (subC M w)

    subC-unbox : ∀ {A A₀ C C' ρ₀ ρ'}
               → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
               → (rel : ρ' ≾ᵣ ρ₀)
               → (v : A₀ <:ᵛ A)
               → (w : C <:ᶜ C')
               → (M : Γ ∷ A ⊢ᶜ⦂ C)
               ----------------------------------------------------
               → Γ ⊢ᶜ⦂ subC (unbox x rel v M) w
                    ≡ᵗʰ unbox x rel v (subC M w)

    -- Sub-effecting the result of a bind is sub-effecting its continuation.
    -- Only the effect half needs an axiom: its value half is derivable from
    -- the eta and associativity rules of `_⨟_`, this one is not.

    coerce-seq-in : ∀ {A B ε ε₁' ε₂'}
                  → (rel : ε₁' ≾ₑ ε₂')
                  → (M : Γ ⊢ᶜ⦂ A ! ε)
                  → (N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε₁')
                  ----------------------------------------------------------
                  → Γ ⊢ᶜ⦂ coerce (·ₑ-monoʳ-≾ₑ rel) (M ⨟ N) ≡ᵗʰ M ⨟ coerce rel N

    -- Handling with a coerced handler value coerces the handled computation
    -- in and the answer out. The handled grade stays fixed: restricting it
    -- would leave the answer's grade above the coerced handler's.

    subV-handle : ∀ {A A₁ B B₁ ε ε' ε₁'}
                → (p : A <:ᵛ A₁) → (pε : ε ≾ₑ ε)
                → (q : B₁ <:ᵛ B) → (s : ε₁' ≾ₑ ε')
                → (M : Γ ⊢ᶜ⦂ A ! ε)
                → (V : Γ ⊢ᵛ⦂ (A₁ ! ε) ⇛ (B₁ ! ε₁'))
                ----------------------------------------------------------------
                → Γ ⊢ᶜ⦂ handle M `with subV V ((p !ₛ pε) ⇛ₛ (q !ₛ s))
                     ≡ᵗʰ subC (handle (subC M (p !ₛ pε)) `with V)
                              (q !ₛ ·ₑ-monoʳ-≾ₑ s)

    -- equations for collapsing successive delays

    delay-zero : ∀ {A ε}
               → (M : Γ ⟨ ιᵣ 0ᴰ ⟩ ⊢ᶜ⦂ A ! ε)
               --------------------------
               → Γ ⊢ᶜ⦂ delay 0ᴰ M
                   ≡ᵗʰ ε-≃ (≃ₑ-sym (≃ₑ-trans (·ₑ-cong ιₑ-zero ≃ₑ-refl) (·ₑ-identityˡ ε)))
                        (C-rename
                          (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ ιᵣ-zero) ∘ʳ ⟨⟩-η-ren)
                          M)

    delay-delay : ∀ {A τ₁ τ₂ ε}
                → (M : Γ ⟨ ιᵣ (τ₁ +ᴰ τ₂) ⟩ ⊢ᶜ⦂ A ! ε)
                ------------------------------------
                → Γ ⊢ᶜ⦂ delay τ₁ (delay τ₂
                           (C-rename
                             (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ ιᵣ-plus) ∘ʳ ⟨⟩-μ-ren)
                             M))
                    ≡ᵗʰ ε-≃ (≃ₑ-trans (·ₑ-cong ιₑ-plus ≃ₑ-refl) (·ₑ-assoc (ιₑ τ₁) (ιₑ τ₂) ε))
                         (delay (τ₁ +ᴰ τ₂) M)

  infix 18 _⊢ᶜ⦂_≡ᵗʰ_
