--------------------------------------------------------------------------
-- Naturality of subsumption at the formers that derive it.             --
--                                                                      --
-- A subsumption commutes with every term former. Where the former has  --
-- an eta rule the commutation is a theorem, not an axiom: the eta rule --
-- re-expands the node around the subsumption and the beta rules        --
-- collapse the copies. The atomic value formers get theirs from        --
-- `subV-refl`, the witness at `Base`/`unit`/`bool`/`nat` being         --
-- reflexive.                                                           --
--------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.EquationalTheory.Naturality (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming.Action S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Substitution    S
open import MonomorphicCalculus.Syntax.Types           S

open import MonomorphicCalculus.Syntax.Terms.Equivalence  S using (var-≡; subV-≡)
open import MonomorphicCalculus.Syntax.Substitution.Laws  S using (sub-wk-≡ᵛ; sub-wk-≡ᶜ)

-- Binder subsumption and its substitution law.

open import MonomorphicCalculus.Syntax.Substitution.Subsumption  S using (subCtx; subCtx-sub)

open import MonomorphicCalculus.EquationalTheory.EquationalTheory S

-- Transporting an equation along syntactic identities of its two sides.

≡ᵗʰ-castᶜ : ∀ {Γ C} {M M' N N' : Γ ⊢ᶜ⦂ C}
          → M ≡ M' → N ≡ N' → Γ ⊢ᶜ⦂ M ≡ᵗʰ N → Γ ⊢ᶜ⦂ M' ≡ᵗʰ N'
≡ᵗʰ-castᶜ refl refl p = p

-- The topmost variable, at its declared grade.

hd : ∀ {Γ A} → Γ ∷ A ⊢ᵛ⦂ A
hd = var (λ _ → ≾ᵣ-refl) Hd


-- The atomic value formers: the witness relates a type to itself, so the
-- subsumption is `subV-refl`. At `Base` it still transports the constant.

subV-const : ∀ {Γ b b'} → (e : b ≡ b') → (c : BaseConstants b)
           -----------------------------------------------------------------
           → Γ ⊢ᵛ⦂ subV (const b c) (Baseₛ e) ≡ᵗʰ const b' (subst BaseConstants e c)
subV-const refl c = subV-refl (Baseₛ refl) (const _ c)

subV-⋆ : ∀ {Γ} → Γ ⊢ᵛ⦂ subV ⋆ unitₛ ≡ᵗʰ ⋆
subV-⋆ = subV-refl unitₛ ⋆

subV-true : ∀ {Γ} → Γ ⊢ᵛ⦂ subV true boolₛ ≡ᵗʰ true
subV-true = subV-refl boolₛ true

subV-false : ∀ {Γ} → Γ ⊢ᵛ⦂ subV false boolₛ ≡ᵗʰ false
subV-false = subV-refl boolₛ false


-- Empty type elimination: the eta rule names the subsumed `absurd` as the
-- body, so the subsumption vanishes.

subC-absurd : ∀ {Γ C C'}
            → (w : C <:ᶜ C')
            → (V : Γ ⊢ᵛ⦂ empty)
            --------------------------------------------------------------
            → Γ ⊢ᶜ⦂ subC (absurd {C = C} V) w ≡ᵗʰ absurd {C = C'} V
subC-absurd w V =
  C-sym (absurd-eta V (subC (absurd hd) w))


-- Boolean elimination: eta at the subsumed node, then beta in each branch.

subC-if : ∀ {Γ C C'}
        → (w : C <:ᶜ C')
        → (V : Γ ⊢ᵛ⦂ bool)
        → (M N : Γ ⊢ᶜ⦂ C)
        --------------------------------------------------------------
        → Γ ⊢ᶜ⦂ subC (if V `then M `else N) w
             ≡ᵗʰ if V `then subC M w `else subC N w
subC-if {Γ} {C} {C'} w V M N =
  C-trans
    (C-sym (≡ᵗʰ-castᶜ (cong₂ (λ X Y → if V `then X `else Y) (fill true) (fill false))
                      (fill V)
                      (if-eta V body)))
    (if-cong V-refl
             (subC-cong (if-beta-true M N))
             (subC-cong (if-beta-false M N)))
  where
    body : Γ ∷ bool ⊢ᶜ⦂ C'
    body = subC (if hd `then C-rename wk-ren M `else C-rename wk-ren N) w

    fill : (U : Γ ⊢ᵛ⦂ bool)
         → body [ split-[] ↦ U ]c ≡ subC (if U `then M `else N) w
    fill U = cong₂ (λ X Y → subC (if U `then X `else Y) w)
                   (sub-wk-≡ᶜ [] U M) (sub-wk-≡ᶜ [] U N)


-- Function application: the domain half of the witness lands on the
-- argument, the codomain half outside: the `SUB-APP` reduction rule,
-- read as an equation.

subV-app : ∀ {Γ A A' C C'}
         → (p : A' <:ᵛ A)
         → (w : C <:ᶜ C')
         → (V : Γ ⊢ᵛ⦂ A ⇒ C)
         → (W : Γ ⊢ᵛ⦂ A')
         ----------------------------------------------------------
         → Γ ⊢ᶜ⦂ subV V (p ⇒ₛ w) · W ≡ᵗʰ subC (V · subV W p) w
subV-app p w V W =
  C-trans
    (app-cong (V-trans (subV-cong (fun-eta V))
                       (subV-fun p w (V-rename wk-ren V · hd)))
              V-refl)
    (≡ᵗʰ-castᶜ refl (cong (λ X → subC X w) body-sub)
               (fun-beta (subC (subCtx p (V-rename wk-ren V · hd)) w) W))
  where
    body-sub : subCtx p (V-rename wk-ren V · hd) [ split-[] ↦ W ]c
             ≡ V · subV W p
    body-sub =
      trans (subCtx-sub p (V-rename wk-ren V · hd) W)
            (cong (_· subV W p) (sub-wk-≡ᵛ [] (subV W p) V))


-- `ε-subst` is a transport with no content, and a subsumption absorbs the
-- effect ordering either side of it carries.

ε-subst-cong : ∀ {Γ A ε ε'} → (e : ε ≡ ε') → {M N : Γ ⊢ᶜ⦂ A ! ε}
             → Γ ⊢ᶜ⦂ M ≡ᵗʰ N
             ------------------------------------------
             → Γ ⊢ᶜ⦂ ε-subst e M ≡ᵗʰ ε-subst e N
ε-subst-cong refl p = p

coerce-ε-subst : ∀ {Γ A ε₁ ε₂ ε₃ ε₄}
               → (e : ε₁ ≡ ε₂) → (e' : ε₃ ≡ ε₄)
               → (c : ε₂ ≾ₑ ε₃) → (c' : ε₁ ≾ₑ ε₄)
               → (M : Γ ⊢ᶜ⦂ A ! ε₁)
               ----------------------------------------------------------
               → Γ ⊢ᶜ⦂ ε-subst e' (coerce c (ε-subst e M)) ≡ᵗʰ coerce c' M
coerce-ε-subst refl refl c c' M = subC-cong C-refl

-- The same for regrading along an equivalence, which is a sub-effecting:
-- stated at the underlying orderings, which unification can read off a term.

ε-≃-cong : ∀ {Γ A ε ε'} → (c : ε ≾ₑ ε') → {M N : Γ ⊢ᶜ⦂ A ! ε}
         → Γ ⊢ᶜ⦂ M ≡ᵗʰ N
         ------------------------------------------
         → Γ ⊢ᶜ⦂ coerce c M ≡ᵗʰ coerce c N
ε-≃-cong c p = subC-cong p

coerce-ε-≃ : ∀ {Γ A ε₁ ε₂ ε₃ ε₄}
           → (e : ε₁ ≾ₑ ε₂) → (e' : ε₃ ≾ₑ ε₄)
           → (c : ε₂ ≾ₑ ε₃) → (c' : ε₁ ≾ₑ ε₄)
           → (M : Γ ⊢ᶜ⦂ A ! ε₁)
           ----------------------------------------------------------
           → Γ ⊢ᶜ⦂ coerce e' (coerce c (coerce e M)) ≡ᵗʰ coerce c' M
coerce-ε-≃ {A = A} e e' c c' M =
  C-trans (subC-cong (subC-trans (<:ᵛ-refl A !ₛ e) (<:ᵛ-refl A !ₛ c)
                                 (<:ᵛ-refl A !ₛ ≾ₑ-trans e c) M))
  (C-trans (subC-trans _ (<:ᵛ-refl A !ₛ e') (<:ᵛ-refl A !ₛ c') M) C-refl)


-- Returning: expand the subsumed `return` by the sequencing eta rule, move
-- the subsumption onto the trailing binder, and collapse the bind. Only the
-- value half enters; the effect half has nowhere to go, `return`'s effect
-- being the unit.

subC-return : ∀ {Γ A A' ε'}
            → (p : A <:ᵛ A')
            → (q : 𝟏ₑ ≾ₑ ε')
            → (V : Γ ⊢ᵛ⦂ A)
            ----------------------------------------------------------
            → Γ ⊢ᶜ⦂ subC (return V) (p !ₛ q) ≡ᵗʰ coerce q (return (subV V p))
subC-return p q V =
  C-trans (seq-eta (subC (return V) (p !ₛ q)))
  (C-trans (ε-≃-cong _ (subC-seq p q (return V) (return hd)))
  (C-trans (ε-≃-cong _ (subC-cong (seq-return V (return (subV hd p)))))
           (coerce-ε-≃ _ _ (·ₑ-monoˡ-≾ₑ q) q (return (subV V p)))))


-- The subsumption of a computation, expanded by the sequencing eta rule: a
-- bind whose continuation returns the subsumed variable. This is what carries
-- a subsumption past a former with a `seq-*` rule.

subC-seq-eta : ∀ {Γ A A' ε₁ ε₂}
             → (v : A <:ᵛ A')
             → (rel : ε₁ ≾ₑ ε₂)
             → (M : Γ ⊢ᶜ⦂ A ! ε₁)
             -------------------------------------------------------------
             → Γ ⊢ᶜ⦂ subC M (v !ₛ rel)
                  ≡ᵗʰ ε-≃ (·ₑ-identityʳ ε₂)
                       (coerce (·ₑ-monoˡ-≾ₑ rel) (M ⨟ return (subV hd v)))
subC-seq-eta v rel M =
  C-trans (seq-eta (subC M (v !ₛ rel)))
          (ε-≃-cong _ (subC-seq v rel M (return hd)))

-- An `ε-subst` in a continuation is one on the composite.

seq-ε-subst : ∀ {Γ A B ε ε' ε''}
            → (e : ε' ≡ ε'')
            → (M : Γ ⊢ᶜ⦂ A ! ε)
            → (N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε')
            ------------------------------------------------------
            → M ⨟ ε-subst e N ≡ ε-subst (cong (ε ·ₑ_) e) (M ⨟ N)
seq-ε-subst refl M N = refl

ε-subst-coerce : ∀ {Γ A ε ε'}
               → (e : ε ≡ ε') → (c : ε ≾ₑ ε') → (M : Γ ⊢ᶜ⦂ A ! ε)
               ---------------------------------------------------
               → Γ ⊢ᶜ⦂ ε-subst e M ≡ᵗʰ coerce c M
ε-subst-coerce refl c M = C-sym (subC-refl _ M)


-- Sequencing, at the result position: a subsumption of a bind is a
-- subsumption of its continuation, relaxing the residual effect grade. The
-- value half is `μᵀ`-naturality and is derived here from the eta and
-- associativity rules; the effect half is the axiom `coerce-seq-in`.

subC-seq-in : ∀ {Γ A B B' ε ε₁' ε₂'}
            → (v : B <:ᵛ B')
            → (q : ε₁' ≾ₑ ε₂')
            → (M : Γ ⊢ᶜ⦂ A ! ε)
            → (N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε₁')
            ----------------------------------------------------------
            → Γ ⊢ᶜ⦂ subC (M ⨟ N) (v !ₛ ·ₑ-monoʳ-≾ₑ q)
                 ≡ᵗʰ M ⨟ subC N (v !ₛ q)
subC-seq-in {Γ} {B' = B'} {ε = ε} {ε₁' = ε₁'} v q M N =
  C-trans (C-sym (subC-trans (v !ₛ ≾ₑ-refl) (<:ᵛ-refl B' !ₛ ·ₑ-monoʳ-≾ₑ q)
                             (v !ₛ ·ₑ-monoʳ-≾ₑ q) (M ⨟ N)))
  (C-trans (subC-cong value-half)
  (C-trans (coerce-seq-in q M (subC N (v !ₛ ≾ₑ-refl)))
           (seq-cong C-refl (subC-trans (v !ₛ ≾ₑ-refl) (<:ᵛ-refl B' !ₛ q)
                                        (v !ₛ q) N))))
  where
    assoc-≾ : ε ·ₑ (ε₁' ·ₑ 𝟏ₑ) ≾ₑ ε ·ₑ ε₁'
    assoc-≾ = ≃ₑ⇒≾ₑ (·ₑ-cong ≃ₑ-refl (·ₑ-identityʳ ε₁'))

    value-half : Γ ⊢ᶜ⦂ subC (M ⨟ N) (v !ₛ ≾ₑ-refl)
                    ≡ᵗʰ M ⨟ subC N (v !ₛ ≾ₑ-refl)
    value-half =
      C-trans
        (C-trans (subC-seq-eta v ≾ₑ-refl (M ⨟ N))
        (C-trans (ε-≃-cong _ (subC-cong
                    (≡ᵗʰ-castᶜ refl (cong (λ X → ε-≃ (≃ₑ-sym (·ₑ-assoc ε ε₁' 𝟏ₑ)) (M ⨟ (N ⨟ X)))
                                          (cong return (subV-≡ var-≡)))
                               (seq-assoc M N (return (subV hd v))))))
                 (coerce-ε-≃ _ _ (·ₑ-monoˡ-≾ₑ ≾ₑ-refl) assoc-≾
                                 (M ⨟ (N ⨟ return (subV hd v))))))
        (C-sym
          (C-trans (seq-cong C-refl (subC-seq-eta v ≾ₑ-refl N))
          (C-trans (seq-cong C-refl (ε-≃-cong _ (subC-refl _ _)))
          (C-trans (C-sym (coerce-seq-in _ M (N ⨟ return (subV hd v))))
                   (≡ᵗʰ-castᶜ refl
                      (cong (λ w → coerce w (M ⨟ (N ⨟ return (subV hd v))))
                            (≾ₑ-irrelevant _ _))
                      C-refl)))))


-- Pattern matching. At a pair scrutinee the beta rule reduces both sides to
-- the same double substitution, a subsumption commuting with substitution on
-- the nose; the eta rule lifts that to an arbitrary scrutinee, both sides
-- being the eta-expansion of the same body.

subC-match-pair : ∀ {Γ A B C C'}
                → (w : C <:ᶜ C')
                → (V : Γ ⊢ᵛ⦂ A)
                → (W : Γ ⊢ᵛ⦂ B)
                → (M : Γ ∷ A ∷ B ⊢ᶜ⦂ C)
                ----------------------------------------------------
                → Γ ⊢ᶜ⦂ subC (match ⦉ V , W ⦊ `with M) w
                     ≡ᵗʰ match ⦉ V , W ⦊ `with subC M w
subC-match-pair w V W M =
  C-trans (subC-cong (match-beta V W M))
          (C-sym (match-beta V W (subC M w)))

subC-match : ∀ {Γ A B C C'}
           → (w : C <:ᶜ C')
           → (V : Γ ⊢ᵛ⦂ A |×| B)
           → (M : Γ ∷ A ∷ B ⊢ᶜ⦂ C)
           ----------------------------------------------------
           → Γ ⊢ᶜ⦂ subC (match V `with M) w ≡ᵗʰ match V `with subC M w
subC-match {Γ} {A} {B} {C} {C'} w V M =
  C-trans
    (C-sym (≡ᵗʰ-castᶜ refl castL (match-eta V bodyL)))
    (C-trans (match-cong V-refl (subC-match-pair w _ _ _))
             (≡ᵗʰ-castᶜ refl castR (match-eta V bodyR)))
  where
    r = cong-ren {Γ'' = [] ∷ A ∷ B} (wk-ren {Δ = Γ} {A = A |×| B})

    bodyL : Γ ∷ (A |×| B) ⊢ᶜ⦂ C'
    bodyL = subC (match hd `with C-rename r M) w

    bodyR : Γ ∷ (A |×| B) ⊢ᶜ⦂ C'
    bodyR = match hd `with subC (C-rename r M) w

    castL : bodyL [ split-[] ↦ V ]c ≡ subC (match V `with M) w
    castL = cong (λ X → subC (match V `with X) w) (sub-wk-≡ᶜ ([] ∷ A ∷ B) V M)

    castR : bodyR [ split-[] ↦ V ]c ≡ match V `with subC M w
    castR = cong (λ X → match V `with subC X w) (sub-wk-≡ᶜ ([] ∷ A ∷ B) V M)


-- Sum elimination, as pattern matching: at an injected scrutinee the beta
-- rules reduce both sides to the same substitution, and the eta rule lifts
-- that to an arbitrary scrutinee.

subC-match+-inl : ∀ {Γ A B C C'}
                → (w : C <:ᶜ C')
                → (V : Γ ⊢ᵛ⦂ A)
                → (M : Γ ∷ A ⊢ᶜ⦂ C)
                → (N : Γ ∷ B ⊢ᶜ⦂ C)
                ------------------------------------------------------------
                → Γ ⊢ᶜ⦂ subC (match+ inl V `inl M `inr N) w
                    ≡ᵗʰ match+ inl V `inl subC M w `inr subC N w
subC-match+-inl w V M N =
  C-trans (subC-cong (match+-beta-inl V M N))
          (C-sym (match+-beta-inl V (subC M w) (subC N w)))

subC-match+-inr : ∀ {Γ A B C C'}
                → (w : C <:ᶜ C')
                → (V : Γ ⊢ᵛ⦂ B)
                → (M : Γ ∷ A ⊢ᶜ⦂ C)
                → (N : Γ ∷ B ⊢ᶜ⦂ C)
                ------------------------------------------------------------
                → Γ ⊢ᶜ⦂ subC (match+ inr V `inl M `inr N) w
                    ≡ᵗʰ match+ inr V `inl subC M w `inr subC N w
subC-match+-inr w V M N =
  C-trans (subC-cong (match+-beta-inr V M N))
          (C-sym (match+-beta-inr V (subC M w) (subC N w)))

subC-match+ : ∀ {Γ A B C C'}
            → (w : C <:ᶜ C')
            → (V : Γ ⊢ᵛ⦂ A |+| B)
            → (M : Γ ∷ A ⊢ᶜ⦂ C)
            → (N : Γ ∷ B ⊢ᶜ⦂ C)
            ------------------------------------------------------------
            → Γ ⊢ᶜ⦂ subC (match+ V `inl M `inr N) w
                ≡ᵗʰ match+ V `inl subC M w `inr subC N w
subC-match+ {Γ} {A} {B} {C} {C'} w V M N =
  C-trans
    (C-sym (≡ᵗʰ-castᶜ refl castL (match+-eta V bodyL)))
    (C-trans (match+-cong V-refl (subC-match+-inl w _ _ _) (subC-match+-inr w _ _ _))
             (≡ᵗʰ-castᶜ refl castR (match+-eta V bodyR)))
  where
    rA = cong-ren {Γ'' = [] ∷ A} (wk-ren {Δ = Γ} {A = A |+| B})
    rB = cong-ren {Γ'' = [] ∷ B} (wk-ren {Δ = Γ} {A = A |+| B})

    bodyL : Γ ∷ (A |+| B) ⊢ᶜ⦂ C'
    bodyL = subC (match+ hd `inl C-rename rA M `inr C-rename rB N) w

    bodyR : Γ ∷ (A |+| B) ⊢ᶜ⦂ C'
    bodyR = match+ hd `inl subC (C-rename rA M) w `inr subC (C-rename rB N) w

    castL : bodyL [ split-[] ↦ V ]c ≡ subC (match+ V `inl M `inr N) w
    castL = cong₂ (λ X Y → subC (match+ V `inl X `inr Y) w)
                  (sub-wk-≡ᶜ ([] ∷ A) V M) (sub-wk-≡ᶜ ([] ∷ B) V N)

    castR : bodyR [ split-[] ↦ V ]c ≡ match+ V `inl subC M w `inr subC N w
    castR = cong₂ (λ X Y → match+ V `inl subC X w `inr subC Y w)
                  (sub-wk-≡ᶜ ([] ∷ A) V M) (sub-wk-≡ᶜ ([] ∷ B) V N)


-- Natural-number elimination, likewise: the beta rules at `zero` and at a
-- successor, lifted to an arbitrary scrutinee by the eta rule.

subC-matchℕ-zero : ∀ {Γ C C'}
                 → (w : C <:ᶜ C')
                 → (M : Γ ⊢ᶜ⦂ C)
                 → (N : Γ ∷ nat ⊢ᶜ⦂ C)
                 ------------------------------------------------------------
                 → Γ ⊢ᶜ⦂ subC (matchℕ zero `zero M `succ N) w
                     ≡ᵗʰ matchℕ zero `zero subC M w `succ subC N w
subC-matchℕ-zero w M N =
  C-trans (subC-cong (matchℕ-beta-zero M N))
          (C-sym (matchℕ-beta-zero (subC M w) (subC N w)))

subC-matchℕ-succ : ∀ {Γ C C'}
                 → (w : C <:ᶜ C')
                 → (V : Γ ⊢ᵛ⦂ nat)
                 → (M : Γ ⊢ᶜ⦂ C)
                 → (N : Γ ∷ nat ⊢ᶜ⦂ C)
                 ------------------------------------------------------------
                 → Γ ⊢ᶜ⦂ subC (matchℕ succ V `zero M `succ N) w
                     ≡ᵗʰ matchℕ succ V `zero subC M w `succ subC N w
subC-matchℕ-succ w V M N =
  C-trans (subC-cong (matchℕ-beta-succ V M N))
          (C-sym (matchℕ-beta-succ V (subC M w) (subC N w)))

subC-matchℕ : ∀ {Γ C C'}
            → (w : C <:ᶜ C')
            → (V : Γ ⊢ᵛ⦂ nat)
            → (M : Γ ⊢ᶜ⦂ C)
            → (N : Γ ∷ nat ⊢ᶜ⦂ C)
            ------------------------------------------------------------
            → Γ ⊢ᶜ⦂ subC (matchℕ V `zero M `succ N) w
                ≡ᵗʰ matchℕ V `zero subC M w `succ subC N w
subC-matchℕ {Γ} {C} {C'} w V M N =
  C-trans
    (C-sym (≡ᵗʰ-castᶜ refl castL (matchℕ-eta V bodyL)))
    (C-trans (matchℕ-cong V-refl (subC-matchℕ-zero w _ _) (subC-matchℕ-succ w _ _ _))
             (≡ᵗʰ-castᶜ refl castR (matchℕ-eta V bodyR)))
  where
    rN = cong-ren {Γ'' = [] ∷ nat} (wk-ren {Δ = Γ} {A = nat})

    bodyL : Γ ∷ nat ⊢ᶜ⦂ C'
    bodyL = subC (matchℕ hd `zero C-rename wk-ren M `succ C-rename rN N) w

    bodyR : Γ ∷ nat ⊢ᶜ⦂ C'
    bodyR = matchℕ hd `zero subC (C-rename wk-ren M) w `succ subC (C-rename rN N) w

    castL : bodyL [ split-[] ↦ V ]c ≡ subC (matchℕ V `zero M `succ N) w
    castL = cong₂ (λ X Y → subC (matchℕ V `zero X `succ Y) w)
                  (sub-wk-≡ᶜ [] V M) (sub-wk-≡ᶜ ([] ∷ nat) V N)

    castR : bodyR [ split-[] ↦ V ]c ≡ matchℕ V `zero subC M w `succ subC N w
    castR = cong₂ (λ X Y → matchℕ V `zero subC X w `succ subC Y w)
                  (sub-wk-≡ᶜ [] V M) (sub-wk-≡ᶜ ([] ∷ nat) V N)


-- List elimination, likewise: the beta rules at `nil` and at a `cons`, lifted
-- to an arbitrary scrutinee by the eta rule.

subC-matchL-nil : ∀ {Γ A C C'}
                → (w : C <:ᶜ C')
                → (M : Γ ⊢ᶜ⦂ C)
                → (N : Γ ∷ A ∷ list A ⊢ᶜ⦂ C)
                ------------------------------------------------------------
                → Γ ⊢ᶜ⦂ subC (matchL nil `nil M `cons N) w
                    ≡ᵗʰ matchL nil `nil subC M w `cons subC N w
subC-matchL-nil w M N =
  C-trans (subC-cong (matchL-beta-nil M N))
          (C-sym (matchL-beta-nil (subC M w) (subC N w)))

subC-matchL-cons : ∀ {Γ A C C'}
                 → (w : C <:ᶜ C')
                 → (V : Γ ⊢ᵛ⦂ A)
                 → (W : Γ ⊢ᵛ⦂ list A)
                 → (M : Γ ⊢ᶜ⦂ C)
                 → (N : Γ ∷ A ∷ list A ⊢ᶜ⦂ C)
                 ------------------------------------------------------------
                 → Γ ⊢ᶜ⦂ subC (matchL cons V W `nil M `cons N) w
                     ≡ᵗʰ matchL cons V W `nil subC M w `cons subC N w
subC-matchL-cons w V W M N =
  C-trans (subC-cong (matchL-beta-cons V W M N))
          (C-sym (matchL-beta-cons V W (subC M w) (subC N w)))

subC-matchL : ∀ {Γ A C C'}
            → (w : C <:ᶜ C')
            → (V : Γ ⊢ᵛ⦂ list A)
            → (M : Γ ⊢ᶜ⦂ C)
            → (N : Γ ∷ A ∷ list A ⊢ᶜ⦂ C)
            ------------------------------------------------------------
            → Γ ⊢ᶜ⦂ subC (matchL V `nil M `cons N) w
                ≡ᵗʰ matchL V `nil subC M w `cons subC N w
subC-matchL {Γ} {A} {C} {C'} w V M N =
  C-trans
    (C-sym (≡ᵗʰ-castᶜ refl castL (matchL-eta V bodyL)))
    (C-trans (matchL-cong V-refl (subC-matchL-nil w _ _) (subC-matchL-cons w _ _ _ _))
             (≡ᵗʰ-castᶜ refl castR (matchL-eta V bodyR)))
  where
    rN = cong-ren {Γ'' = [] ∷ A ∷ list A} (wk-ren {Δ = Γ} {A = list A})

    bodyL : Γ ∷ list A ⊢ᶜ⦂ C'
    bodyL = subC (matchL hd `nil C-rename wk-ren M `cons C-rename rN N) w

    bodyR : Γ ∷ list A ⊢ᶜ⦂ C'
    bodyR = matchL hd `nil subC (C-rename wk-ren M) w `cons subC (C-rename rN N) w

    castL : bodyL [ split-[] ↦ V ]c ≡ subC (matchL V `nil M `cons N) w
    castL = cong₂ (λ X Y → subC (matchL V `nil X `cons Y) w)
                  (sub-wk-≡ᶜ [] V M) (sub-wk-≡ᶜ ([] ∷ A ∷ list A) V N)

    castR : bodyR [ split-[] ↦ V ]c ≡ matchL V `nil subC M w `cons subC N w
    castR = cong₂ (λ X Y → matchL V `nil subC X w `cons subC Y w)
                  (sub-wk-≡ᶜ [] V M) (sub-wk-≡ᶜ ([] ∷ A ∷ list A) V N)
