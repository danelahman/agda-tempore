------------------------------------------------------------------------
-- Naturality of subsumption at the formers that derive it.            --
--                                                                    --
-- A subsumption commutes with every term former. Where the former has --
-- an eta rule the commutation is a theorem, not an axiom: the eta rule --
-- re-expands the node around the subsumption and the beta rules        --
-- collapse the copies. The atomic value formers get theirs from        --
-- `subV-refl`, the witness at `Base`/`Unit`/`Bool` being reflexive.    --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module EquationalTheory.Naturality (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.RenActions    S
open import Syntax.Renamings     S
open import Syntax.Substitutions S
open import Syntax.Types         S

open import Syntax.Terms.Equivalence  S using (var-≡; subV-≡)
open import Syntax.Substitutions.Laws S using (sub-wk-≡ᵛ; sub-wk-≡ᶜ)

-- Binder subsumption and its substitution law.

open import Syntax.Substitutions.Subsumption S using (subCtx; subCtx-sub)

open import EquationalTheory.EquationalTheory S

-- Transporting an equation along syntactic identities of its two sides.

==-castᶜ : ∀ {Γ C} {M M' N N' : Γ ⊢C⦂ C}
         → M ≡ M' → N ≡ N' → Γ ⊢C⦂ M == N → Γ ⊢C⦂ M' == N'
==-castᶜ refl refl p = p

-- The topmost variable, at its declared grade.

hd : ∀ {Γ A} → Γ ∷ A ⊢V⦂ A
hd = var (λ _ → ≾ᵣ-refl) Hd


-- The atomic value formers: the witness relates a type to itself, so the
-- subsumption is `subV-refl`. At `Base` it still transports the constant.

subV-const : ∀ {Γ b b'} → (e : b ≡ b') → (c : BaseConstants b)
           -----------------------------------------------------------------
           → Γ ⊢V⦂ subV (const c) (Baseₛ e) == const (subst BaseConstants e c)
subV-const refl c = subV-refl (Baseₛ refl) (const c)

subV-⋆ : ∀ {Γ} → Γ ⊢V⦂ subV ⋆ Unitₛ == ⋆
subV-⋆ = subV-refl Unitₛ ⋆

subV-true : ∀ {Γ} → Γ ⊢V⦂ subV true Boolₛ == true
subV-true = subV-refl Boolₛ true

subV-false : ∀ {Γ} → Γ ⊢V⦂ subV false Boolₛ == false
subV-false = subV-refl Boolₛ false


-- Empty type elimination: the eta rule names the subsumed `absurd` as the
-- body, so the subsumption vanishes.

subC-absurd : ∀ {Γ C C'}
            → (w : C <:ᶜ C')
            → (V : Γ ⊢V⦂ Empty)
            --------------------------------------------------------------
            → Γ ⊢C⦂ subC (absurd {C = C} V) w == absurd {C = C'} V
subC-absurd w V =
  C-sym (absurd-eta V (subC (absurd hd) w))


-- Boolean elimination: eta at the subsumed node, then beta in each branch.

subC-if : ∀ {Γ C C'}
        → (w : C <:ᶜ C')
        → (V : Γ ⊢V⦂ Bool)
        → (M N : Γ ⊢C⦂ C)
        --------------------------------------------------------------
        → Γ ⊢C⦂ subC (if V `then M `else N) w
             == if V `then subC M w `else subC N w
subC-if {Γ} {C} {C'} w V M N =
  C-trans
    (C-sym (==-castᶜ (cong₂ (λ X Y → if V `then X `else Y) (fill true) (fill false))
                     (fill V)
                     (if-eta V body)))
    (if-cong V-refl
             (subC-cong (if-beta-true M N))
             (subC-cong (if-beta-false M N)))
  where
    body : Γ ∷ Bool ⊢C⦂ C'
    body = subC (if hd `then C-rename wk-ren M `else C-rename wk-ren N) w

    fill : (U : Γ ⊢V⦂ Bool)
         → body [ split-[] ↦ U ]c ≡ subC (if U `then M `else N) w
    fill U = cong₂ (λ X Y → subC (if U `then X `else Y) w)
                   (sub-wk-≡ᶜ [] U M) (sub-wk-≡ᶜ [] U N)


-- Function application: eta-expand the subsumed function, push the
-- subsumption through the abstraction, and beta-reduce. The domain half
-- lands on the argument and the codomain half outside — Phase 3's `SUB-APP`
-- reduction rule, read as an equation.

subV-app : ∀ {Γ A A' C C'}
         → (p : A' <:ᵛ A)
         → (w : C <:ᶜ C')
         → (V : Γ ⊢V⦂ A ⇒ C)
         → (W : Γ ⊢V⦂ A')
         ----------------------------------------------------------
         → Γ ⊢C⦂ subV V (p ⇒ₛ w) · W == subC (V · subV W p) w
subV-app p w V W =
  C-trans
    (app-cong (V-trans (subV-cong (fun-eta V))
                       (subV-lam p w (V-rename wk-ren V · hd)))
              V-refl)
    (==-castᶜ refl (cong (λ X → subC X w) body-sub)
              (fun-beta (subC (subCtx p (V-rename wk-ren V · hd)) w) W))
  where
    body-sub : subCtx p (V-rename wk-ren V · hd) [ split-[] ↦ W ]c
             ≡ V · subV W p
    body-sub =
      trans (subCtx-sub p (V-rename wk-ren V · hd) W)
            (cong (_· subV W p) (sub-wk-≡ᵛ [] (subV W p) V))


-- `ε-subst` is a transport with no content, and a subsumption absorbs the
-- effect ordering either side of it carries.

ε-subst-cong : ∀ {Γ A ε ε'} → (e : ε ≡ ε') → {M N : Γ ⊢C⦂ A ‼ ε}
             → Γ ⊢C⦂ M == N
             ------------------------------------------
             → Γ ⊢C⦂ ε-subst e M == ε-subst e N
ε-subst-cong refl p = p

coerce-ε-subst : ∀ {Γ A ε₁ ε₂ ε₃ ε₄}
               → (e : ε₁ ≡ ε₂) → (e' : ε₃ ≡ ε₄)
               → (c : ε₂ ≾ₑ ε₃) → (c' : ε₁ ≾ₑ ε₄)
               → (M : Γ ⊢C⦂ A ‼ ε₁)
               ----------------------------------------------------------
               → Γ ⊢C⦂ ε-subst e' (coerce c (ε-subst e M)) == coerce c' M
coerce-ε-subst refl refl c c' M = subC-cong C-refl


-- Returning: expand the subsumed `return` by the sequencing eta rule, move
-- the subsumption onto the trailing binder, and collapse the bind. Only the
-- value half enters — the effect half has nowhere to go, `return`'s effect
-- being the unit.

subC-return : ∀ {Γ A A' ε'}
            → (p : A <:ᵛ A')
            → (q : uₑ ≾ₑ ε')
            → (V : Γ ⊢V⦂ A)
            ----------------------------------------------------------
            → Γ ⊢C⦂ subC (return V) (p ‼ₛ q) == coerce q (return (subV V p))
subC-return p q V =
  C-trans (seq-eta (subC (return V) (p ‼ₛ q)))
  (C-trans (ε-subst-cong _ (subC-seq p q (return V) (return hd)))
  (C-trans (ε-subst-cong _ (subC-cong (seq-return V (return (subV hd p)))))
           (coerce-ε-subst _ _ (·ₑ-monoˡ-≾ₑ q) q (return (subV V p)))))


-- The subsumption of a computation, expanded by the sequencing eta rule: a
-- bind whose continuation returns the subsumed variable. This is what carries
-- a subsumption past a former with a `seq-*` rule.

subC-seq-eta : ∀ {Γ A A' ε₁ ε₂}
             → (v : A <:ᵛ A')
             → (rel : ε₁ ≾ₑ ε₂)
             → (M : Γ ⊢C⦂ A ‼ ε₁)
             -------------------------------------------------------------
             → Γ ⊢C⦂ subC M (v ‼ₛ rel)
                  == ε-subst (·ₑ-identityʳ ε₂)
                       (coerce (·ₑ-monoˡ-≾ₑ rel) (M ⨟ return (subV hd v)))
subC-seq-eta v rel M =
  C-trans (seq-eta (subC M (v ‼ₛ rel)))
          (ε-subst-cong _ (subC-seq v rel M (return hd)))

-- An `ε-subst` in a continuation is one on the composite.

seq-ε-subst : ∀ {Γ A B ε ε' ε''}
            → (e : ε' ≡ ε'')
            → (M : Γ ⊢C⦂ A ‼ ε)
            → (N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
            ------------------------------------------------------
            → M ⨟ ε-subst e N ≡ ε-subst (cong (ε ·ₑ_) e) (M ⨟ N)
seq-ε-subst refl M N = refl

ε-subst-coerce : ∀ {Γ A ε ε'}
               → (e : ε ≡ ε') → (c : ε ≾ₑ ε') → (M : Γ ⊢C⦂ A ‼ ε)
               ---------------------------------------------------
               → Γ ⊢C⦂ ε-subst e M == coerce c M
ε-subst-coerce refl c M = C-sym (subC-refl _ M)


-- Sequencing, at the result position: a subsumption of a bind is a
-- subsumption of its continuation, relaxing the residual effect grade. The
-- value half is `μᵀ`-naturality and is derived here from the eta and
-- associativity rules; the effect half is the axiom `coerce-seq`.

subC-seq-in : ∀ {Γ A B B' ε ε₁' ε₂'}
            → (v : B <:ᵛ B')
            → (q : ε₁' ≾ₑ ε₂')
            → (M : Γ ⊢C⦂ A ‼ ε)
            → (N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε₁')
            ----------------------------------------------------------
            → Γ ⊢C⦂ subC (M ⨟ N) (v ‼ₛ ·ₑ-monoʳ-≾ₑ q)
                 == M ⨟ subC N (v ‼ₛ q)
subC-seq-in {Γ} {B' = B'} {ε = ε} {ε₁' = ε₁'} v q M N =
  C-trans (C-sym (subC-trans (v ‼ₛ ≾ₑ-refl) (<:ᵛ-refl B' ‼ₛ ·ₑ-monoʳ-≾ₑ q)
                             (v ‼ₛ ·ₑ-monoʳ-≾ₑ q) (M ⨟ N)))
  (C-trans (subC-cong value-half)
  (C-trans (coerce-seq q M (subC N (v ‼ₛ ≾ₑ-refl)))
           (seq-cong C-refl (subC-trans (v ‼ₛ ≾ₑ-refl) (<:ᵛ-refl B' ‼ₛ q)
                                        (v ‼ₛ q) N))))
  where
    assoc-≾ : ε ·ₑ (ε₁' ·ₑ uₑ) ≾ₑ ε ·ₑ ε₁'
    assoc-≾ = ≾ₑ-reflexive (cong (ε ·ₑ_) (·ₑ-identityʳ ε₁'))

    value-half : Γ ⊢C⦂ subC (M ⨟ N) (v ‼ₛ ≾ₑ-refl)
                    == M ⨟ subC N (v ‼ₛ ≾ₑ-refl)
    value-half =
      C-trans
        (C-trans (subC-seq-eta v ≾ₑ-refl (M ⨟ N))
        (C-trans (ε-subst-cong _ (subC-cong
                    (==-castᶜ refl (cong (λ X → ε-subst (sym (·ₑ-assoc ε ε₁' uₑ)) (M ⨟ (N ⨟ X)))
                                         (cong return (subV-≡ var-≡)))
                              (seq-assoc M N (return (subV hd v))))))
                 (coerce-ε-subst _ _ (·ₑ-monoˡ-≾ₑ ≾ₑ-refl) assoc-≾
                                 (M ⨟ (N ⨟ return (subV hd v))))))
        (C-sym
          (C-trans (seq-cong C-refl (subC-seq-eta v ≾ₑ-refl N))
          (C-trans (seq-cong C-refl (ε-subst-cong _ (subC-refl _ _)))
          (C-trans (==-castᶜ refl (seq-ε-subst _ M (N ⨟ return (subV hd v))) C-refl)
                   (ε-subst-coerce _ assoc-≾ (M ⨟ (N ⨟ return (subV hd v))))))))


-- Pattern matching. At a pair scrutinee the beta rule reduces both sides to
-- the same double substitution, a subsumption commuting with substitution on
-- the nose; the eta rule lifts that to an arbitrary scrutinee, both sides
-- being the eta-expansion of the same body.

subC-match-pair : ∀ {Γ A B C C'}
                → (w : C <:ᶜ C')
                → (V : Γ ⊢V⦂ A)
                → (W : Γ ⊢V⦂ B)
                → (M : Γ ∷ A ∷ B ⊢C⦂ C)
                ----------------------------------------------------
                → Γ ⊢C⦂ subC (match ⦉ V , W ⦊ `in M) w
                     == match ⦉ V , W ⦊ `in subC M w
subC-match-pair w V W M =
  C-trans (subC-cong (match-beta V W M))
          (C-sym (match-beta V W (subC M w)))

subC-match : ∀ {Γ A B C C'}
           → (w : C <:ᶜ C')
           → (V : Γ ⊢V⦂ A |×| B)
           → (M : Γ ∷ A ∷ B ⊢C⦂ C)
           ----------------------------------------------------
           → Γ ⊢C⦂ subC (match V `in M) w == match V `in subC M w
subC-match {Γ} {A} {B} {C} {C'} w V M =
  C-trans
    (C-sym (==-castᶜ refl castL (match-eta V bodyL)))
    (C-trans (match-cong V-refl (subC-match-pair w _ _ _))
             (==-castᶜ refl castR (match-eta V bodyR)))
  where
    r = cong-ren {Γ'' = [] ∷ A ∷ B} (wk-ren {Δ = Γ} {A = A |×| B})

    bodyL : Γ ∷ (A |×| B) ⊢C⦂ C'
    bodyL = subC (match hd `in C-rename r M) w

    bodyR : Γ ∷ (A |×| B) ⊢C⦂ C'
    bodyR = match hd `in subC (C-rename r M) w

    castL : bodyL [ split-[] ↦ V ]c ≡ subC (match V `in M) w
    castL = cong (λ X → subC (match V `in X) w) (sub-wk-≡ᶜ ([] ∷ A ∷ B) V M)

    castR : bodyR [ split-[] ↦ V ]c ≡ match V `in subC M w
    castR = cong (λ X → match V `in subC X w) (sub-wk-≡ᶜ ([] ∷ A ∷ B) V M)
