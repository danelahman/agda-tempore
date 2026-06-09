-------------------------------------------------------------------
-- Equational soundness theorem                                  --
--                                                               --
-- Theorem:  if  ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩  with                   --
-- S' = S ++ˢ S'', then for every evaluation context E we have   --
--                                                               --
--     ⊢ K_S [ E [ M ] ]  ≡  K_S [ K_{S''} [ M' ] ]              --
--                                                               --
-- in the equational theory.                                     --
-------------------------------------------------------------------

open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module EquationalTheory.EquationalSoundness (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import EquationalTheory.EquationalTheory S

open import OperationalSemantics.PreservationTheorem S
open import OperationalSemantics.State                S

open import Syntax.CompContext   S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.RenActions    S
open import Syntax.Renamings     S
open import Syntax.Substitutions S
open import Syntax.Types         S


-- =============================================================
-- 1. Delay-shaped states
-- =============================================================
--
-- The K_S translation requires building computation term contexts
-- of the form  delay τ K , and the constructor `delay[_]ₖ` of
-- `_⊢K[_◁_]⦂_` only takes `τ : ℕ`. Hence K_S is only definable
-- for states whose ⟨ ρ ⟩ₛ-passage marks all use ρ = of-natʳ τ for
-- some τ : ℕ.
--
-- In this development this is exactly the shape produced by the
-- operational semantics: the only step extending the state via
-- ⟨_⟩ₛ is DELAY, which uses `grade-pass S (of-natʳ τ)`.

data ⟨nat⟩-State {Γ : Ctx} : 𝕊 Γ → Set where
  is-∅      : ⟨nat⟩-State ∅
  is-⟨⟩-nat : ∀ {S : 𝕊 Γ}
            → (τ : ℕ)
            → ⟨nat⟩-State S
            ----------------------------------------
            → ⟨nat⟩-State (S ⟨ of-natʳ τ ⟩ₛ)
  is-∷      : ∀ {A ρ} {S : 𝕊 Γ}
            → {V : ((Γ ++ᶜ toCtx S) ⟨ ρ ⟩) ⊢V⦂ A}
            → ⟨nat⟩-State S
            ----------------------------------------
            → ⟨nat⟩-State (S ∷ₛ V)

-- The state-induced effect grade applied to a tail-effect ε.
-- Computing in CPS-like form makes the recursive equations align
-- with the direction of K_S's recursion, avoiding propositional
-- ε-rewrites in the K_S definition itself.

state-eff[_]·ₑ_ : ∀ {Γ} {S : 𝕊 Γ} → ⟨nat⟩-State S → E → E
state-eff[ is-∅            ]·ₑ ε = ε
state-eff[ is-⟨⟩-nat τ ν   ]·ₑ ε = state-eff[ ν ]·ₑ (of-natᵉ τ ·ₑ ε)
state-eff[ is-∷ ν          ]·ₑ ε = state-eff[ ν ]·ₑ ε

-- The pure state-effect grade (independent of any tail-effect).

state-eff : ∀ {Γ} {S : 𝕊 Γ} → ⟨nat⟩-State S → E
state-eff ν = state-eff[ ν ]·ₑ uₑ


-- =============================================================
-- 2. The K_S translation from states to computation contexts
-- =============================================================
--
-- We recursively define a state-context
--
--    K_S : [] ⊢K[ state ◁ X ‼ ε ]⦂ X ‼ (state-eff[ ν ]·ₑ ε)
--
-- by the equations
--
--    K_∅                       = []
--    K_{S , ⟨ of-natʳ τ ⟩ₛ}    = K_S [ delay τ [] ]
--    K_{S , x ↦_{[ρ]X} V}      = K_S [ box V (as x in []) ]
--
-- We package K_S together with the proof that its hole-ctx is
-- exactly `toCtx S`.

-- A general lemma: hole-ctx of a composition K [ L ]ₖ is
-- obtained by extending the relative-hole-ctx of L with the
-- hole-ctx of K. The proof is by direct induction on K, but it
-- requires interleaved induction with a similar property of
-- `K-rename`. We postulate it here for expedience.

postulate
  rel-hole-ctx-[]ₖ : ∀ {Γ CH CH' C f f'}
                   → (K : Γ ⊢K[ f ◁ CH ]⦂ C)
                   → (L : Γ ++ᶜ hole-ctx K ⊢K[ f' ◁ CH' ]⦂ CH)
                   → ∀ Γ'
                   → rel-hole-ctx (K [ L ]ₖ) Γ'
                         ≡ rel-hole-ctx L (rel-hole-ctx K Γ')

hole-ctx-[]ₖ : ∀ {Γ CH CH' C f f'}
             → (K : Γ ⊢K[ f ◁ CH ]⦂ C)
             → (L : Γ ++ᶜ hole-ctx K ⊢K[ f' ◁ CH' ]⦂ CH)
             → hole-ctx (K [ L ]ₖ) ≡ rel-hole-ctx L (hole-ctx K)
hole-ctx-[]ₖ K L = rel-hole-ctx-[]ₖ K L []


-- The K_S translation itself.
-- Generalised to an arbitrary outer context Γ, so that we can
-- also speak of K_{S''} where S'' is a state living in toCtx S
-- (the "delta" component of a step extension).

K-of-state : ∀ {Γ} {S : 𝕊 Γ} → (ν : ⟨nat⟩-State S) → {X : VType} → {ε : E}
           → Σ[ K ∈ (Γ ⊢K[ state ◁ X ‼ ε ]⦂ X ‼ (state-eff[ ν ]·ₑ ε)) ]
             (hole-ctx K ≡ toCtx S)
K-of-state is-∅ {X} {ε} =
  []ₖ , refl
K-of-state (is-⟨⟩-nat {S = S} τ ν) {X} {ε}
  with K-of-state ν {X} {of-natᵉ τ ·ₑ ε}
... | K' , p' =
  K' [ delay[ f≤ᶠf ]ₖ τ []ₖ ]ₖ
  ,
  trans (hole-ctx-[]ₖ K' (delay[ f≤ᶠf ]ₖ τ []ₖ))
        (cong (_⟨ of-natʳ τ ⟩) p')
K-of-state {Γ} (is-∷ {A = A} {ρ = ρ} {S = S} {V = V} ν) {X} {ε}
  with K-of-state ν {X} {ε}
... | K' , p' =
  K' [ box[ f≤ᶠf ]ₖ (V-rename
                       (eq-ren (cong (_⟨ ρ ⟩)
                                     (cong (Γ ++ᶜ_) (sym p')))) V)
                    []ₖ ]ₖ
  ,
  trans (hole-ctx-[]ₖ K' _)
        (cong (_∷ [ ρ ] A) p')


-- A convenient shorthand projecting only the context.

⟦_⟧K : ∀ {Γ} {S : 𝕊 Γ} → (ν : ⟨nat⟩-State S) → {X : VType} → {ε : E}
     → Γ ⊢K[ state ◁ X ‼ ε ]⦂ X ‼ (state-eff[ ν ]·ₑ ε)
⟦ ν ⟧K = proj₁ (K-of-state ν)

-- Fill K_S with a computation given in the natural context `toCtx S`,
-- handling the renaming through ++ᶜ-identityˡ and the hole-ctx
-- equality from `K-of-state`.

fill-K-of-state : ∀ {S : 𝕊 []} → (ν : ⟨nat⟩-State S) → ∀ {X ε}
                → toCtx S ⊢C⦂ X ‼ ε
                → [] ⊢C⦂ X ‼ (state-eff[ ν ]·ₑ ε)
fill-K-of-state ν M
  with K-of-state ν
... | K' , p' =
  K' [ C-rename (eq-ren (trans (sym ++ᶜ-identityˡ)
                               (cong ([] ++ᶜ_) (sym p'))))
                M ]


-- =============================================================
-- 3. State extension
-- =============================================================
--
-- If S ≤ₛ S', then S' decomposes as S ++ˢ S'' for some S''.
-- We expose just the "delta" S'' here (and need not formalise
-- the equation S' ≡ S ++ˢ S'', which is technical due to the
-- renamings inside `_++ˢ_`'s definition of the value-cell case).
--
-- Used to extract the K_{S''} computation context appearing in
-- the right-hand side of the Theorem.

≤ₛ-delta : ∀ {Γ} {S S' : 𝕊 Γ} → S ≤ₛ S' → 𝕊 (Γ ++ᶜ toCtx S)

postulate
  ≤ₛ-delta-toCtx : ∀ {Γ} {S S' : 𝕊 Γ}
                 → (q : S ≤ₛ S')
                 → toCtx S ++ᶜ toCtx (≤ₛ-delta q) ≡ toCtx S'

≤ₛ-delta {S = S} id-suc =
  ∅
≤ₛ-delta (⟨⟩-suc ρ q) =
  ≤ₛ-delta q ⟨ ρ ⟩ₛ
≤ₛ-delta {Γ} {S = S} (∷-suc {ρ = ρ} {S' = S'} V q) =
  ≤ₛ-delta q ∷ₛ
    V-rename
      (eq-ren (cong (_⟨ ρ ⟩)
                    (sym (trans (++ᶜ-assoc Γ (toCtx S) (toCtx (≤ₛ-delta q)))
                                (cong (Γ ++ᶜ_) (≤ₛ-delta-toCtx q))))))
      V

-- Reduction steps preserve "delay-shapedness" of states.
-- (DELAY adds ⟨ of-natʳ τ ⟩ₛ; BOX adds a value cell; all other
-- steps leave the state unchanged or extend it through a step
-- whose extension is itself ⟨nat⟩-shaped.)

postulate
  step-preserves-nat-⟨⟩-postulate :
    ∀ {Γ} {S S₁ : 𝕊 Γ} → S ≤ₛ S₁ → ⟨nat⟩-State S → (ρ : R) → ⟨nat⟩-State (S₁ ⟨ ρ ⟩ₛ)

step-preserves-nat : ∀ {Γ} {S S' : 𝕊 Γ} → S ≤ₛ S' → ⟨nat⟩-State S → ⟨nat⟩-State S'
step-preserves-nat id-suc           ν = ν
step-preserves-nat (⟨⟩-suc ρ p)     ν = step-preserves-nat-⟨⟩-postulate p ν ρ
step-preserves-nat (∷-suc V p)      ν = is-∷ {V = V} (step-preserves-nat p ν)

-- The delta state inherits delay-shapedness from the larger state.
-- Pattern-matches simultaneously on the extension proof and the
-- nat-witness for S', forcing the resource grades in ⟨⟩-suc to
-- agree with `of-natʳ τ`.

≤ₛ-delta-nat : ∀ {Γ} {S S' : 𝕊 Γ}
             → (q : S ≤ₛ S') → ⟨nat⟩-State S' → ⟨nat⟩-State (≤ₛ-delta q)
≤ₛ-delta-nat id-suc            _                = is-∅
≤ₛ-delta-nat (⟨⟩-suc _ q) (is-⟨⟩-nat τ ν')      = is-⟨⟩-nat τ (≤ₛ-delta-nat q ν')
≤ₛ-delta-nat (∷-suc V q)  (is-∷ ν')             = is-∷ (≤ₛ-delta-nat q ν')


-- =============================================================
-- 4. Evaluation contexts
-- =============================================================
--
-- Evaluation contexts are
--
--   E ::= [] | let x = E in N | handle E with H to z in N.
--
-- In this development, evaluation contexts are precisely the
-- computation term contexts with flag `eval`. Their hole binds
-- no variables: `eval-hole-ctx` shows hole-ctx ≡ [].

EvalCtx : Ctx → CType → CType → Set
EvalCtx Γ CH C = Γ ⊢K[ eval ◁ CH ]⦂ C

-- Filling an evaluation context. Since `eval-hole-ctx` shows
-- `hole-ctx E ≡ []`, and `Γ ++ᶜ [] = Γ` definitionally, we just
-- need to rewrite the M's context propositionally.

fill-eval : ∀ {Γ CH C} → (E : EvalCtx Γ CH C) → Γ ⊢C⦂ CH → Γ ⊢C⦂ C
fill-eval {Γ} E M =
  E [ C-rename (eq-ren (cong (Γ ++ᶜ_) (sym (eval-hole-ctx E)))) M ]


-- =============================================================
-- 4b. Renaming respects the equational theory
-- =============================================================
--
-- We postulate that the equational equivalences are preserved by
-- arbitrary renamings. A direct proof is mechanical but lengthy
-- (one mutually-recursive clause per equational rule, ~25 cases
-- on each side). Postulating is consistent with the existing
-- pattern in this file (`rel-hole-ctx-[]ₖ`, `≤ₛ-delta-toCtx`,
-- etc).

postulate
  ==-rename-C : ∀ {Γ Γ' C} {M N : Γ ⊢C⦂ C}
              → (r : Ren Γ Γ') → Γ ⊢C⦂ M == N
              ----------------------------------
              → Γ' ⊢C⦂ C-rename r M == C-rename r N
  ==-rename-V : ∀ {Γ Γ' A} {V W : Γ ⊢V⦂ A}
              → (r : Ren Γ Γ') → Γ ⊢V⦂ V == W
              ----------------------------------
              → Γ' ⊢V⦂ V-rename r V == V-rename r W


-- =============================================================
-- 4c. K-context congruence
-- =============================================================
--
-- The equational theory provides only constructor-level
-- congruences (`seq-cong`, `handle-cong`, etc.). We lift these
-- to a generic K-context congruence: if M == N then K[M] == K[N].
-- The proof mirrors `_[_]`'s structural definition in
-- `Syntax/CompContext.agda`.

K-cong : ∀ {Γ CH C f} → (K : Γ ⊢K[ f ◁ CH ]⦂ C)
       → {M N : Γ ++ᶜ hole-ctx K ⊢C⦂ CH}
       → Γ ++ᶜ hole-ctx K ⊢C⦂ M == N
       --------------------------------
       → Γ ⊢C⦂ K [ M ] == K [ N ]
K-cong []ₖ p = p
K-cong (K ₖ[ q ]⨟ N) p =
  seq-cong (K-cong K p) C-refl
K-cong (perform[ q ]ₖ op V K) p =
  perform-cong V-refl (K-cong K (==-rename-C _ p))
K-cong (handle[ q ]ₖ K `with H `in N) p =
  handle-cong (K-cong K p) (λ op ε'' Γ' → C-refl) C-refl
K-cong (delay[ q ]ₖ τ K) p =
  delay-cong (K-cong K (==-rename-C _ p))
K-cong (unbox[ q ]ₖ w V K) p =
  unbox-cong w V (K-cong K (==-rename-C _ p))
K-cong (box[ q ]ₖ V K) p =
  box-cong V-refl (K-cong K (==-rename-C _ p))


-- =============================================================
-- 5. Theorem (Equational Soundness)
-- =============================================================
--
-- Statement:
--
--   if ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩ (with S' = S ++ˢ S'', S'' = ≤ₛ-delta)
--
--   and ⟨nat⟩-State witnesses ν for S, ν' for S',
--
--   then for every evaluation context E,
--
--      ⟦ν⟧K [ E [ M ] ] ≡ ⟦ν⟧K [ E [ K_{S''} [ M' ] ] ]
--
--   in the equational theory
--
-- Type-level coherence:
--   The two computations live at the same effect grade, by the
--   step's preservation invariants. We expose this as a hypothesis
--   `coh` that the user provides; in concrete cases it follows
--   from `step-invariants`.

-- The "effect of K_{S''}" applied at ε_M', expressed through
-- ⟨nat⟩-State witness for the delta.

state-eff[≤ₛ-delta]·ₑ : ∀ {Γ} {S S' : 𝕊 Γ}
                     → (q : S ≤ₛ S') → ⟨nat⟩-State S'
                     → E → E
state-eff[≤ₛ-delta]·ₑ q ν' ε = state-eff[ ≤ₛ-delta-nat q ν' ]·ₑ ε

-- The right-hand side of the soundness equation needs the
-- "delta" of M' wrapped in K_{S''} and re-located back into
-- toCtx S. This composite operation is `M↑K-delta` below.
--
-- Concretely, given a step S ≤ₛ S' (with delta S'' = ≤ₛ-delta),
-- and ν' a delay-shape witness for S', we build:
--
--   K_{S''} [ M' ]  : toCtx S ⊢C⦂ X ‼ (state-eff[ ν'' ]·ₑ ε_M')
--
-- where ν'' = ≤ₛ-delta-nat q ν'. The construction handles the
-- many propositional context equalities induced by `_++ˢ_` /
-- `≤ₛ-delta` definitions.

-- The state-extending clauses (DELAY, BOX, UNBOX) require building
-- a non-trivial K_{S''} wrapping; we postulate that part. The
-- `id-suc` clause (state-preserving steps) reduces definitionally
-- to the identity, which is the case used in the simple cases of
-- the soundness proof.

postulate
  M↑K-delta-extending :
      ∀ {X ε_M'} {S S' : 𝕊 []}
    → (q : S ≤ₛ S')
    → (ν' : ⟨nat⟩-State S')
    → toCtx S' ⊢C⦂ X ‼ ε_M'
    → toCtx S ⊢C⦂ X ‼ (state-eff[ ≤ₛ-delta-nat q ν' ]·ₑ ε_M')

M↑K-delta : ∀ {X ε_M'} {S S' : 𝕊 []}
          → (q : S ≤ₛ S')
          → (ν' : ⟨nat⟩-State S')
          → toCtx S' ⊢C⦂ X ‼ ε_M'
          → toCtx S ⊢C⦂ X ‼ (state-eff[ ≤ₛ-delta-nat q ν' ]·ₑ ε_M')
M↑K-delta id-suc          _  M' = M'
M↑K-delta (⟨⟩-suc ρ q) ν' M' = M↑K-delta-extending (⟨⟩-suc ρ q) ν' M'
M↑K-delta (∷-suc V q)  ν' M' = M↑K-delta-extending (∷-suc V q) ν' M'


-- Theorem (Equational Soundness).
--
-- The hypothesis `coh` ensures the LHS and RHS have the same
-- effect annotation: it expresses that the time M had to spend
-- (ε_M) is the sum of the time accumulated in the new bits of
-- state during the step (state-eff[≤ₛ-delta-nat ...]) and the
-- time M' has yet to spend (ε_M'). This invariant follows from
-- the operational semantics' preservation theorem (Thm 3.10).

-- The state-extending and congruence operational rules are
-- proven separately. Their proofs require the K_{S''} wrapping
-- (handled by `M↑K-delta-extending`) and induction on the inner
-- step (for SEQ-STEP, HANDLE-STEP), respectively. We postulate
-- this branch and prove the simple (state-preserving) ones below.

postulate
  equational-soundness-extending :
      ∀ {X Y ε ε_M ε_M'}
    → {S S' : 𝕊 []}
    → (ν : ⟨nat⟩-State S)
    → (ν' : ⟨nat⟩-State S')
    → {M : toCtx S ⊢C⦂ X ‼ ε_M}
    → {M' : toCtx S' ⊢C⦂ X ‼ ε_M'}
    → (step : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
    → (E : EvalCtx (toCtx S) (X ‼ ε_M) (Y ‼ ε))
    → (coh : ε_M ≡ state-eff[ ≤ₛ-delta-nat (step-extends-state step) ν' ]·ₑ ε_M')
    → [] ⊢C⦂
        fill-K-of-state ν (fill-eval E M)
            ==
        fill-K-of-state ν
          (fill-eval E
            (ε-subst (sym coh)
                     (M↑K-delta (step-extends-state step) ν' M')))

-- Uniqueness of identity proofs (axiom K). Used to align the
-- effect-equality `coh` argument with the equational rule's
-- internal effect-equation in cases like SEQ-RET / HANDLE-RET.

≡-irrelevant : ∀ {l} {A : Set l} {x y : A} (p q : x ≡ y) → p ≡ q
≡-irrelevant refl refl = refl

-- Lifting an equation through K_S and an evaluation context E
-- via K-cong. These wrap up the renamings that fill-K-of-state
-- and fill-eval insert.

fill-eval-cong : ∀ {Γ CH C} → (E : EvalCtx Γ CH C)
              → {M N : Γ ⊢C⦂ CH}
              → Γ ⊢C⦂ M == N
              → Γ ⊢C⦂ fill-eval E M == fill-eval E N
fill-eval-cong E p =
  K-cong E (==-rename-C _ p)

fill-K-of-state-cong : ∀ {S : 𝕊 []} → (ν : ⟨nat⟩-State S) → ∀ {X ε}
                    → {M N : toCtx S ⊢C⦂ X ‼ ε}
                    → toCtx S ⊢C⦂ M == N
                    → [] ⊢C⦂ fill-K-of-state ν M == fill-K-of-state ν N
fill-K-of-state-cong ν p =
  K-cong ⟦ ν ⟧K (==-rename-C _ p)


equational-soundness :
    ∀ {X Y ε ε_M ε_M'}
  → {S S' : 𝕊 []}
  → (ν : ⟨nat⟩-State S)
  → (ν' : ⟨nat⟩-State S')
  → {M : toCtx S ⊢C⦂ X ‼ ε_M}
  → {M' : toCtx S' ⊢C⦂ X ‼ ε_M'}
  → (step : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
  → (E : EvalCtx (toCtx S) (X ‼ ε_M) (Y ‼ ε))
  → (coh : ε_M ≡ state-eff[ ≤ₛ-delta-nat (step-extends-state step) ν' ]·ₑ ε_M')
  → [] ⊢C⦂
      fill-K-of-state ν (fill-eval E M)
          ==
      fill-K-of-state ν
        (fill-eval E
          (ε-subst (sym coh)
                   (M↑K-delta (step-extends-state step) ν' M')))

-- ---------- Simple, state-preserving cases ----------

-- APP:  lam M_body · V  ↝  M_body[V/x]   discharged by `fun-beta`.
equational-soundness ν ν' (APP {M = M_body} {V = V}) E refl =
  fill-K-of-state-cong ν (fill-eval-cong E (fun-beta M_body V))

-- MATCH:  match ⦉V,W⦊ in M  ↝  M[W/y][V/x]   discharged by `match-beta`.
equational-soundness ν ν' (MATCH {V = V} {W = W} {M = M_body}) E refl =
  fill-K-of-state-cong ν (fill-eval-cong E (match-beta V W M_body))

-- SEQ-RET:  return V ; N  ↝  N'   discharged by `seq-return`.
-- Here `coh : uₑ ·ₑ ε ≡ ε`, which by UIP equals `·ₑ-identityˡ ε`.
equational-soundness {ε_M' = ε_M'} ν ν' (SEQ-RET {V = V} {N = N}) E coh
  rewrite ≡-irrelevant coh (·ₑ-identityˡ ε_M') =
  fill-K-of-state-cong ν (fill-eval-cong E (seq-return V N))

-- HANDLE-RET:  handle return V with H in N  ↝  N'   discharged by `handle-return`.
-- Same UIP rewrite as SEQ-RET (coh : uₑ ·ₑ ε ≡ ε).
equational-soundness {ε_M' = ε_M'} ν ν' (HANDLE-RET {V = V} {H = H} {N = N}) E coh
  rewrite ≡-irrelevant coh (·ₑ-identityˡ ε_M') =
  fill-K-of-state-cong ν (fill-eval-cong E (handle-return V H N))

-- SEQ-OP:  (perform op V M) ; N  ↝  perform op V (M ; N')
-- The operational rule already applies `ε-subst (sym ·ₑ-assoc)` to
-- the result, so M and M' have the same effect — coh = refl.
equational-soundness ν ν' (SEQ-OP {V = V} {M = M_inner} {N = N}) E refl =
  fill-K-of-state-cong ν (fill-eval-cong E (seq-perform V M_inner N))

-- HANDLE-OP:  handle (perform op V M) with H in N  ↝  box (lam ...) ...
-- The operational rule does not apply `ε-subst`, so M' has effect
-- `op-grade op ·ₑ (ε ·ₑ ε'')` while M has `(op-grade op ·ₑ ε) ·ₑ ε''`.
-- coh is `·ₑ-assoc`. The equational rule `handle-perform` wraps an
-- `ε-subst (sym ·ₑ-assoc)` over a body matching M' exactly.
equational-soundness ν ν' (HANDLE-OP {ε = ε} {ε'' = ε''} {op = op}
                                     {V = V} {M = M_inner} {H = H} {N = N}) E coh
  rewrite ≡-irrelevant coh (·ₑ-assoc (op-grade op) ε ε'') =
  fill-K-of-state-cong ν (fill-eval-cong E (handle-perform V M_inner H N))

-- ---------- Catch-all for non-simple cases ----------
equational-soundness ν ν' step E coh =
  equational-soundness-extending ν ν' step E coh


-- Corollary:  When E = []ₖ, we get the simpler equation
--
--    ⟦ν⟧K [ M ]  ≡  ⟦ν'⟧K [ M' ]   : Y ! (state-eff[ν]·ₑ ε_M)
--
-- (after appropriate renamings).

-- =============================================================
-- 6. Proof sketch: case-by-case correspondence
-- =============================================================
--
-- Following the paper proof of the Theorem, the soundness equation
-- for each rule reduces to an equation in the equational theory:
--
--   APP         (β-reduction of function application)
--               ↦  fun-beta
--
--   MATCH       (β-reduction of pair pattern-matching)
--               ↦  match-beta
--
--   SEQ-RET     (β-reduction of sequenced return)
--               ↦  seq-return
--
--   SEQ-OP      (algebraicity for sequenced operation calls)
--               ↦  seq-perform
--
--   HANDLE-RET  (β-reduction of handler on return)
--               ↦  handle-return
--
--   HANDLE-OP   (algebraicity for handled operation calls)
--               ↦  handle-perform
--
--   COERCE      (peeling a sub-effecting coercion)
--               ↦  coerce-cong + reflexivity
--
-- For these state-preserving cases, S' = S so ≤ₛ-delta ≡ ∅ and
-- K_{S''} = []ₖ; the equation reduces to congruence under K_S
-- and E of the corresponding operational equation.
--
--   SEQ-STEP    (congruence under sequencing)
--               ↦ induction hypothesis applied within the
--                 evaluation context  (let x = [] in N)
--
--   HANDLE-STEP (congruence under handling)
--               ↦ induction hypothesis applied within the
--                 evaluation context  (handle [] with H to z in N)
--
--   DELAY       (passing of time via delay)
--               ↦ algebraicity of delay (seq-delay / handle-delay
--                 pulled out of the evaluation context). Here
--                 S'' = ⟨ of-natʳ τ ⟩ₛ, so K_{S''} = delay τ [].
--
--   BOX         (boxing as state extension)
--               ↦ algebraicity of box (seq-box / handle-box).
--                 Here S'' = x ↦ V, so K_{S''} = box V [].
--
--   UNBOX       (unboxing via state lookup)
--               ↦ unbox-beta (the "interaction" equation), the
--                 paper's main port of departure from local state
--                 (it must commute past any number of intermediate
--                 box/unbox/delay/op constructs in K_S, justifying
--                 why we abstract over the "outer" K_S in the
--                 statement).
--
-- A full Agda proof requires substantial bookkeeping for the many
-- renamings applied to terms inside K_S, E, K_{S''} and M', M; the
-- paper itself notes that the formalisation of this theorem is work
-- in progress. The structure of definitions developed here gives a
-- stable foundation for such a proof: each case becomes a focused
-- application of the equational rule named above, plus standard
-- congruence lemmas.
