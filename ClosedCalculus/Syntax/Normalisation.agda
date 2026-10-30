------------------------------------------------------------------------
-- Subsumption is confined to the reconciliation points.               --
--                                                                     --
-- Every derivation has one with the same erasure in which `subV` and  --
-- `subC` occur only where a sub-derivation must meet a type it does   --
-- not itself determine: an application's argument, a `perform`'s      --
-- parameter, the head and tail of a `cons`, the operands of a `cmp`,  --
-- the branches of `if`, `caseℕ`, `case+` and `caseL`, the base and    --
-- step of `recℕ` and `recL`, a handler's clauses and its              --
-- continuation, and the root.                                         --
-- `NfV`/`NfC` pin those positions and `C-normal-form` is the theorem. --
--                                                                     --
-- The tool is context subsumption along `_≼ᶜ_`, which lowers binder   --
-- types and lock grades at once. It is a statement about derivations: --
-- nothing in the substitution calculus may call it, since it rebuilds --
-- every variable.                                                     --
------------------------------------------------------------------------

open import Data.Product

open import Relation.Nullary using (¬_)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module ClosedCalculus.Syntax.Normalisation (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import ClosedCalculus.Syntax.Contexts S
open import ClosedCalculus.Syntax.Erasure  S
open import ClosedCalculus.Syntax.Terms    S
open import ClosedCalculus.Syntax.Types    S

-- Monotonicity of the two grade products in both arguments

·ᵣ-mono : ∀ {ρ ρ' ρ'' ρ'''} → ρ ≾ᵣ ρ' → ρ'' ≾ᵣ ρ''' → ρ ·ᵣ ρ'' ≾ᵣ ρ' ·ᵣ ρ'''
·ᵣ-mono p q = ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ p) (·ᵣ-monoʳ-≾ᵣ q)

·ₑ-mono : ∀ {ε ε' ε'' ε'''} → ε ≾ₑ ε' → ε'' ≾ₑ ε''' → ε ·ₑ ε'' ≾ₑ ε' ·ₑ ε'''
·ₑ-mono p q = ≾ₑ-trans (·ₑ-monoˡ-≾ₑ p) (·ₑ-monoʳ-≾ₑ q)


-- Context subsumption: pointwise on binder types and lock grades.

infix 4 _≼ᶜ_

data _≼ᶜ_ : Ctx → Ctx → Set where
  ≼-[] : [] ≼ᶜ []
  ≼-∷  : ∀ {Γ₀ Γ₁ A₀ A₁} → Γ₀ ≼ᶜ Γ₁ → A₀ <:ᵛ A₁ → Γ₀ ∷ A₀ ≼ᶜ Γ₁ ∷ A₁
  ≼-⟨⟩ : ∀ {Γ₀ Γ₁ ρ₀ ρ₁} → Γ₀ ≼ᶜ Γ₁ → ρ₀ ≾ᵣ ρ₁ → Γ₀ ⟨ ρ₀ ⟩ ≼ᶜ Γ₁ ⟨ ρ₁ ⟩

≼ᶜ-refl : (Γ : Ctx) → Γ ≼ᶜ Γ
≼ᶜ-refl []        = ≼-[]
≼ᶜ-refl (Γ ∷ A)   = ≼-∷ (≼ᶜ-refl Γ) (<:ᵛ-refl A)
≼ᶜ-refl (Γ ⟨ ρ ⟩) = ≼-⟨⟩ (≼ᶜ-refl Γ) ≾ᵣ-refl

-- A variable of the supertype context occurs in the subtype one at the
-- same position, at a subtype and after no more elapsed grade.

record Lookup≼ (Γ₀ : Ctx) {Γ₁ : Ctx} {A : VType} {ρ : R} (x : A ∈[ ρ ] Γ₁) : Set where
  constructor lkp
  field
    {lty} : VType
    {lgr} : R
    lvar  : lty ∈[ lgr ] Γ₀
    lsub  : lty <:ᵛ A
    lbnd  : lgr ≾ᵣ ρ
    lpos  : var-pos lvar ≡ var-pos x

open Lookup≼

≼ᶜ-lookup : ∀ {Γ₀ Γ₁ A ρ} → Γ₀ ≼ᶜ Γ₁ → (x : A ∈[ ρ ] Γ₁) → Lookup≼ Γ₀ x
≼ᶜ-lookup ≼-[] ()
≼ᶜ-lookup (≼-∷ c p) Hd = lkp Hd p ≾ᵣ-refl refl
≼ᶜ-lookup (≼-∷ c p) (Tl-∷ x) with ≼ᶜ-lookup c x
... | lkp y s b e = lkp (Tl-∷ y) s b (cong suc e)
≼ᶜ-lookup (≼-⟨⟩ c r) (Tl-⟨⟩ x) with ≼ᶜ-lookup c x
... | lkp y s b e = lkp (Tl-⟨⟩ y) s (·ᵣ-mono b r) e


-- Normal derivations: `subV`/`subC` only at the reconciliation points.

data NfV : ∀ {Γ A} → Γ ⊢V⦂ A → Set
data NfC : ∀ {Γ A ε} → Γ ⊢C⦂ A ‼ ε → Set

data NfV where

  varⁿ   : ∀ {Γ A ρ} {f : ¬ Eternal A → ρ ≾ᵣ uᵣ} {x : A ∈[ ρ ] Γ}
         → NfV (var f x)

  constⁿ : ∀ {Γ B} {c : BaseConstants B} → NfV {Γ} (const c)

  ⋆ⁿ     : ∀ {Γ} → NfV {Γ} ⋆

  trueⁿ  : ∀ {Γ} → NfV {Γ} true

  falseⁿ : ∀ {Γ} → NfV {Γ} false

  zeroⁿ  : ∀ {Γ} → NfV {Γ} zero

  succⁿ  : ∀ {Γ} {V : Γ ⊢V⦂ Nat} → NfV V → NfV (succ V)

  pairⁿ  : ∀ {Γ A B} {V : Γ ⊢V⦂ A} {W : Γ ⊢V⦂ B}
         → NfV V → NfV W → NfV ⦉ V , W ⦊

  inlⁿ   : ∀ {Γ A B} {V : Γ ⊢V⦂ A} → NfV V → NfV (inl {B = B} V)

  inrⁿ   : ∀ {Γ A B} {V : Γ ⊢V⦂ B} → NfV V → NfV (inr {A = A} V)

  nilⁿ   : ∀ {Γ A} → NfV {Γ} (nil {A = A})

  -- the head and the tail meet at the element type

  consⁿ  : ∀ {Γ A A₁ A₂} {V : Γ ⊢V⦂ A₁} {W : Γ ⊢V⦂ A₂}
             {p : A₁ <:ᵛ A} {q : A₂ <:ᵛ |List| A}
         → NfV V → NfV W → NfV (cons (subV V p) (subV W q))

  lamⁿ   : ∀ {Γ A B ε} {M : Γ ∷ A ⊢C⦂ B ‼ ε} → NfC M → NfV (lam M)

data NfC where

  returnⁿ  : ∀ {Γ A} {V : Γ ⊢V⦂ A} → NfV V → NfC (return V)

  seqⁿ     : ∀ {Γ A B ε ε'} {M : Γ ⊢C⦂ A ‼ ε} {N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
           → NfC M → NfC N → NfC (M ⨟ N)

  -- the argument meets the domain the function fixes

  appⁿ     : ∀ {Γ A A' B ε} {V : Γ ⊢V⦂ A ⇒ B ‼ ε} {W : Γ ⊢V⦂ A'} {p : A' <:ᵛ A}
           → NfV V → NfV W → NfC (V · subV W p)

  matchⁿ   : ∀ {Γ A B C ε} {V : Γ ⊢V⦂ A |×| B} {N : Γ ∷ A ∷ B ⊢C⦂ C ‼ ε}
           → NfV V → NfC N → NfC (match V `in N)

  absurdⁿ  : ∀ {Γ A ε} {V : Γ ⊢V⦂ Empty} → NfV V → NfC (absurd {C = A ‼ ε} V)

  -- the operands meet at the compared type

  cmpⁿ     : ∀ {Γ A A₁ A₂ ⋈} {V : Γ ⊢V⦂ A₁} {W : Γ ⊢V⦂ A₂}
               {p : A₁ <:ᵛ A} {q : A₂ <:ᵛ A} {et : Eternal A}
           → NfV V → NfV W → NfC (cmp ⋈ (subV V p) (subV W q) et)

  -- the branches meet at the type the `if` is used at

  ifⁿ      : ∀ {Γ A ε A₁ ε₁ A₂ ε₂} {V : Γ ⊢V⦂ Bool}
               {M : Γ ⊢C⦂ A₁ ‼ ε₁} {N : Γ ⊢C⦂ A₂ ‼ ε₂}
               {p : (A₁ ‼ ε₁) <:ᶜ (A ‼ ε)} {q : (A₂ ‼ ε₂) <:ᶜ (A ‼ ε)}
           → NfV V → NfC M → NfC N
           → NfC (if V `then subC M p `else subC N q)

  -- likewise for the branches of a `caseℕ` and of a `case+`

  caseℕⁿ   : ∀ {Γ A ε A₁ ε₁ A₂ ε₂} {V : Γ ⊢V⦂ Nat}
               {M : Γ ⊢C⦂ A₁ ‼ ε₁} {N : Γ ∷ Nat ⊢C⦂ A₂ ‼ ε₂}
               {p : (A₁ ‼ ε₁) <:ᶜ (A ‼ ε)} {q : (A₂ ‼ ε₂) <:ᶜ (A ‼ ε)}
           → NfV V → NfC M → NfC N
           → NfC (caseℕ V `zero subC M p `succ subC N q)

  -- the base and the step meet at the recursion's type, which the step's
  -- binder fixes

  recℕⁿ    : ∀ {Γ B ε A₁ ε₁ A₂ ε₂} {V : Γ ⊢V⦂ Nat}
               {M : Γ ⊢C⦂ A₁ ‼ ε₁} {N : (Γ ⟨ ⊤ᵣ ⟩ ∷ Nat) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ A₂ ‼ ε₂}
               {p : (A₁ ‼ ε₁) <:ᶜ (B ‼ ε)} {q : (A₂ ‼ ε₂) <:ᶜ (B ‼ ε)}
               {r : ε ·ₑ ε ≾ₑ ε}
           → NfV V → NfC M → NfC N
           → NfC (recℕ V (subC M p) (subC N q) r)

  case+ⁿ   : ∀ {Γ A B A' ε A₁ ε₁ A₂ ε₂} {V : Γ ⊢V⦂ A |+| B}
               {M : Γ ∷ A ⊢C⦂ A₁ ‼ ε₁} {N : Γ ∷ B ⊢C⦂ A₂ ‼ ε₂}
               {p : (A₁ ‼ ε₁) <:ᶜ (A' ‼ ε)} {q : (A₂ ‼ ε₂) <:ᶜ (A' ‼ ε)}
           → NfV V → NfC M → NfC N
           → NfC (case+ V `inl subC M p `inr subC N q)

  caseLⁿ   : ∀ {Γ A A' ε A₁ ε₁ A₂ ε₂} {V : Γ ⊢V⦂ |List| A}
               {M : Γ ⊢C⦂ A₁ ‼ ε₁} {N : Γ ∷ A ∷ |List| A ⊢C⦂ A₂ ‼ ε₂}
               {p : (A₁ ‼ ε₁) <:ᶜ (A' ‼ ε)} {q : (A₂ ‼ ε₂) <:ᶜ (A' ‼ ε)}
           → NfV V → NfC M → NfC N
           → NfC (caseL V `nil subC M p `cons subC N q)

  recLⁿ    : ∀ {Γ A B ε A₁ ε₁ A₂ ε₂} {V : Γ ⊢V⦂ |List| A}
               {M : Γ ⊢C⦂ A₁ ‼ ε₁}
               {N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ A₂ ‼ ε₂}
               {p : (A₁ ‼ ε₁) <:ᶜ (B ‼ ε)} {q : (A₂ ‼ ε₂) <:ᶜ (B ‼ ε)}
               {r : ε ·ₑ ε ≾ₑ ε}
           → NfV V → NfC M → NfC N
           → NfC (recL V (subC M p) (subC N q) r)

  -- the parameter meets the ground type the operation fixes; the slack is
  -- non-trivial because ground types include the box modality

  performⁿ : ∀ {Γ A ε A' op} {V : Γ ⊢V⦂ A'} {p : A' <:ᵛ type-of-gtype (param op)}
               {M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
           → NfV V → NfC M → NfC (perform op (subV V p) M)

  delayⁿ   : ∀ {Γ A ε τ} {M : Γ ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε} → NfC M → NfC (delay τ M)

  -- the clauses and the continuation meet at the handler's result type; the
  -- clauses' effects are fixed by the rule, the continuation's is not

  handleⁿ  : ∀ {Γ A B ε ε₁ B₁}
               {M : Γ ⊢C⦂ A ‼ ε}
               {Bh : Op → E → VType} {εh : Op → E → E}
               {H : (op : Op) → (ε'' : E) →
                      Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                      ⊢C⦂ Bh op ε'' ‼ εh op ε''}
               {p : (op : Op) → (ε'' : E) →
                      (Bh op ε'' ‼ εh op ε'') <:ᶜ (B ‼ (op-grade op ·ₑ ε''))}
               {N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B₁ ‼ ε₁} {q : B₁ <:ᵛ B}
           → NfC M
           → ((op : Op) → (ε'' : E) → NfC (H op ε''))
           → NfC N
           → NfC (handle M `with (λ op ε'' → subC (H op ε'') (p op ε''))
                           `in (subC N (q ‼ₛ ≾ₑ-refl)))

  -- the continuation binds the payload at its declared type

  unboxⁿ   : ∀ {Γ A ε A₀ ρ₀ ρ'} {x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ} {rel : ρ' ≾ᵣ ρ₀}
               {N : Γ ∷ A₀ ⊢C⦂ A ‼ ε}
           → NfC N → NfC (unbox x rel (<:ᵛ-refl A₀) N)

  boxⁿ     : ∀ {Γ A ε A₁ ρ} {V : Γ ⟨ ρ ⟩ ⊢V⦂ A₁} {N : Γ ∷ [ ρ ] A₁ ⊢C⦂ A ‼ ε}
           → NfV V → NfC N → NfC (box _ V N)


-- A normal derivation in a subtype context, with its residual subtyping
-- and the erasure it shares with the derivation it came from.

record NfResV (Γ₀ : Ctx) {Γ : Ctx} {A : VType} (V : Γ ⊢V⦂ A) : Set where
  constructor nfv
  field
    {rty} : VType
    rtm   : Γ₀ ⊢V⦂ rty
    rsub  : rty <:ᵛ A
    rnf   : NfV rtm
    rer   : ⌊ rtm ⌋ᵛ ≡ ⌊ V ⌋ᵛ

record NfResC (Γ₀ : Ctx) {Γ : Ctx} {A : VType} {ε : E} (M : Γ ⊢C⦂ A ‼ ε) : Set where
  constructor nfc
  field
    {rvt} : VType
    {ref} : E
    rtm   : Γ₀ ⊢C⦂ rvt ‼ ref
    rsubv : rvt <:ᵛ A
    rsube : ref ≾ₑ ε
    rnf   : NfC rtm
    rer   : ⌊ rtm ⌋ᶜ ≡ ⌊ M ⌋ᶜ

open NfResV
open NfResC


-- Context subsumption: a normal derivation over a context is one over
-- any context below it, at a subtype and with the same erasure.

V-subCtx : ∀ {Γ₀ Γ₁ A} → Γ₀ ≼ᶜ Γ₁ → {V : Γ₁ ⊢V⦂ A} → NfV V → NfResV Γ₀ V
C-subCtx : ∀ {Γ₀ Γ₁ A ε} → Γ₀ ≼ᶜ Γ₁ → {M : Γ₁ ⊢C⦂ A ‼ ε} → NfC M → NfResC Γ₀ M

V-subCtx c (varⁿ {f = f} {x = x}) with ≼ᶜ-lookup c x
... | lkp y s b e =
  nfv (var (λ ¬et → ≾ᵣ-trans b (f (λ et → ¬et (<:ᵛ-eternalˡ s et)))) y)
      s varⁿ (cong var e)
V-subCtx c (constⁿ {c = b}) =
  nfv (const b) (<:ᵛ-refl _) constⁿ refl
V-subCtx c ⋆ⁿ =
  nfv ⋆ Unitₛ ⋆ⁿ refl
V-subCtx c trueⁿ =
  nfv true Boolₛ trueⁿ refl
V-subCtx c falseⁿ =
  nfv false Boolₛ falseⁿ refl
V-subCtx c zeroⁿ =
  nfv zero Natₛ zeroⁿ refl
V-subCtx c (succⁿ nV) with V-subCtx c nV
... | nfv V' Natₛ n e =
  nfv (succ V') Natₛ (succⁿ n) (cong succ e)
V-subCtx c (pairⁿ nV nW) with V-subCtx c nV | V-subCtx c nW
... | nfv V' s₁ n₁ e₁ | nfv W' s₂ n₂ e₂ =
  nfv ⦉ V' , W' ⦊ (s₁ |×|ₛ s₂) (pairⁿ n₁ n₂) (cong₂ ⦉_,_⦊ e₁ e₂)
V-subCtx c (inlⁿ nV) with V-subCtx c nV
... | nfv V' s n e =
  nfv (inl V') (s |+|ₛ <:ᵛ-refl _) (inlⁿ n) (cong inl e)
V-subCtx c (inrⁿ nV) with V-subCtx c nV
... | nfv V' s n e =
  nfv (inr V') (<:ᵛ-refl _ |+|ₛ s) (inrⁿ n) (cong inr e)
V-subCtx c nilⁿ =
  nfv nil (<:ᵛ-refl _) nilⁿ refl
V-subCtx c (consⁿ {p = p} {q = q} nV nW) with V-subCtx c nV | V-subCtx c nW
... | nfv V' s₁ n₁ e₁ | nfv W' s₂ n₂ e₂ =
  nfv (cons (subV V' (<:ᵛ-trans s₁ p)) (subV W' (<:ᵛ-trans s₂ q))) (<:ᵛ-refl _)
      (consⁿ n₁ n₂) (cong₂ cons e₁ e₂)
V-subCtx c (lamⁿ {A = A} nM) with C-subCtx (≼-∷ c (<:ᵛ-refl A)) nM
... | nfc M' sv se n e =
  nfv (lam M') (<:ᵛ-refl A ⇒ₛ (sv ‼ₛ se)) (lamⁿ n) (cong lam e)

C-subCtx c (returnⁿ nV) with V-subCtx c nV
... | nfv V' s n e =
  nfc (return V') s ≾ₑ-refl (returnⁿ n) (cong return e)
C-subCtx c (seqⁿ nM nN) with C-subCtx c nM
... | nfc M' sA sε nM' eM with C-subCtx (≼-∷ (≼-⟨⟩ c (map-monotoneᵉ sε)) sA) nN
...   | nfc N' sB sε' nN' eN =
  nfc (M' ⨟ N') sB (·ₑ-mono sε sε') (seqⁿ nM' nN') (cong₂ _⨟_ eM eN)
C-subCtx c (appⁿ {p = p} nV nW) with V-subCtx c nV
... | nfv V' (sd ⇒ₛ (sv ‼ₛ se)) nV' eV with V-subCtx c nW
...   | nfv W' sw nW' eW =
  nfc (V' · subV W' (<:ᵛ-trans sw (<:ᵛ-trans p sd))) sv se
      (appⁿ nV' nW') (cong₂ _·_ eV eW)
C-subCtx c (matchⁿ nV nN) with V-subCtx c nV
... | nfv V' (s₁ |×|ₛ s₂) nV' eV with C-subCtx (≼-∷ (≼-∷ c s₁) s₂) nN
...   | nfc N' sv se nN' eN =
  nfc (match V' `in N') sv se (matchⁿ nV' nN') (cong₂ match_`in_ eV eN)
C-subCtx c (absurdⁿ nV) with V-subCtx c nV
... | nfv V' Emptyₛ nV' eV =
  nfc (absurd V') (<:ᵛ-refl _) ≾ₑ-refl (absurdⁿ nV') (cong absurd eV)
C-subCtx c (cmpⁿ {⋈ = ⋈} {p = p} {q = q} {et = et} nV nW)
  with V-subCtx c nV | V-subCtx c nW
... | nfv V' s₁ n₁ e₁ | nfv W' s₂ n₂ e₂ =
  nfc (cmp ⋈ (subV V' (<:ᵛ-trans s₁ p)) (subV W' (<:ᵛ-trans s₂ q)) et) (<:ᵛ-refl _)
      ≾ₑ-refl (cmpⁿ n₁ n₂) (cong₂ (cmp ⋈) e₁ e₂)
C-subCtx c (ifⁿ {p = p} {q = q} nV nM nN) with V-subCtx c nV
... | nfv V' Boolₛ nV' eV with C-subCtx c nM | C-subCtx c nN
...   | nfc M' sv₁ se₁ nM' eM | nfc N' sv₂ se₂ nN' eN =
  nfc (if V' `then subC M' (<:ᶜ-trans (sv₁ ‼ₛ se₁) p)
             `else subC N' (<:ᶜ-trans (sv₂ ‼ₛ se₂) q))
      (<:ᵛ-refl _) ≾ₑ-refl (ifⁿ nV' nM' nN')
      (cong₃ (λ a b d → if a `then b `else d) eV eM eN)
C-subCtx c (caseℕⁿ {p = p} {q = q} nV nM nN) with V-subCtx c nV
... | nfv V' Natₛ nV' eV with C-subCtx c nM | C-subCtx (≼-∷ c Natₛ) nN
...   | nfc M' sv₁ se₁ nM' eM | nfc N' sv₂ se₂ nN' eN =
  nfc (caseℕ V' `zero subC M' (<:ᶜ-trans (sv₁ ‼ₛ se₁) p)
                `succ subC N' (<:ᶜ-trans (sv₂ ‼ₛ se₂) q))
      (<:ᵛ-refl _) ≾ₑ-refl (caseℕⁿ nV' nM' nN')
      (cong₃ (λ a b d → caseℕ a `zero b `succ d) eV eM eN)
C-subCtx c (recℕⁿ {B = B} {p = p} {q = q} {r = r} nV nM nN) with V-subCtx c nV
... | nfv V' Natₛ nV' eV
      with C-subCtx c nM
         | C-subCtx (≼-∷ (≼-⟨⟩ (≼-∷ (≼-⟨⟩ c ≾ᵣ-refl) Natₛ) ≾ᵣ-refl) (<:ᵛ-refl B)) nN
...   | nfc M' sv₁ se₁ nM' eM | nfc N' sv₂ se₂ nN' eN =
  nfc (recℕ V' (subC M' (<:ᶜ-trans (sv₁ ‼ₛ se₁) p))
               (subC N' (<:ᶜ-trans (sv₂ ‼ₛ se₂) q)) r)
      (<:ᵛ-refl _) ≾ₑ-refl (recℕⁿ nV' nM' nN')
      (cong₃ (λ a b d → recℕ a b d) eV eM eN)
C-subCtx c (case+ⁿ {p = p} {q = q} nV nM nN) with V-subCtx c nV
... | nfv V' (s₁ |+|ₛ s₂) nV' eV
      with C-subCtx (≼-∷ c s₁) nM | C-subCtx (≼-∷ c s₂) nN
...   | nfc M' sv₁ se₁ nM' eM | nfc N' sv₂ se₂ nN' eN =
  nfc (case+ V' `inl subC M' (<:ᶜ-trans (sv₁ ‼ₛ se₁) p)
                `inr subC N' (<:ᶜ-trans (sv₂ ‼ₛ se₂) q))
      (<:ᵛ-refl _) ≾ₑ-refl (case+ⁿ nV' nM' nN')
      (cong₃ (λ a b d → case+ a `inl b `inr d) eV eM eN)
C-subCtx c (caseLⁿ {p = p} {q = q} nV nM nN) with V-subCtx c nV
... | nfv V' (|List|ₛ s) nV' eV
      with C-subCtx c nM | C-subCtx (≼-∷ (≼-∷ c s) (|List|ₛ s)) nN
...   | nfc M' sv₁ se₁ nM' eM | nfc N' sv₂ se₂ nN' eN =
  nfc (caseL V' `nil subC M' (<:ᶜ-trans (sv₁ ‼ₛ se₁) p)
                `cons subC N' (<:ᶜ-trans (sv₂ ‼ₛ se₂) q))
      (<:ᵛ-refl _) ≾ₑ-refl (caseLⁿ nV' nM' nN')
      (cong₃ (λ a b d → caseL a `nil b `cons d) eV eM eN)
C-subCtx c (recLⁿ {B = B} {p = p} {q = q} {r = r} nV nM nN) with V-subCtx c nV
... | nfv V' (|List|ₛ s) nV' eV
      with C-subCtx c nM
         | C-subCtx (≼-∷ (≼-⟨⟩ (≼-∷ (≼-∷ (≼-⟨⟩ c ≾ᵣ-refl) s) (|List|ₛ s)) ≾ᵣ-refl)
                         (<:ᵛ-refl B)) nN
...   | nfc M' sv₁ se₁ nM' eM | nfc N' sv₂ se₂ nN' eN =
  nfc (recL V' (subC M' (<:ᶜ-trans (sv₁ ‼ₛ se₁) p))
               (subC N' (<:ᶜ-trans (sv₂ ‼ₛ se₂) q)) r)
      (<:ᵛ-refl _) ≾ₑ-refl (recLⁿ nV' nM' nN')
      (cong₃ (λ a b d → recL a b d) eV eM eN)
C-subCtx c (performⁿ {op = op} {p = p} nV nM) with V-subCtx c nV
... | nfv V' s nV' eV
      with C-subCtx (≼-∷ (≼-⟨⟩ c ≾ᵣ-refl) (<:ᵛ-refl _)) nM
...   | nfc M' sv se nM' eM =
  nfc (perform op (subV V' (<:ᵛ-trans s p)) M') sv (·ₑ-monoʳ-≾ₑ se)
      (performⁿ nV' nM') (cong₂ (perform op) eV eM)
C-subCtx c (delayⁿ {τ = τ} nM) with C-subCtx (≼-⟨⟩ c ≾ᵣ-refl) nM
... | nfc M' sv se nM' eM =
  nfc (delay τ M') sv (·ₑ-monoʳ-≾ₑ se) (delayⁿ nM') (cong (delay τ) eM)
C-subCtx c (handleⁿ {p = p} {q = q} nM nH nN) with C-subCtx c nM
... | nfc M' sA sε nM' eM
      with C-subCtx (≼-∷ (≼-⟨⟩ c (map-monotoneᵉ sε)) sA) nN
...   | nfc N' sB sε₁ nN' eN =
  nfc (handle M' `with (λ op ε'' →
         subC (rtm (hr op ε''))
              (<:ᶜ-trans (rsubv (hr op ε'') ‼ₛ rsube (hr op ε'')) (p op ε'')))
                 `in (subC N' (<:ᵛ-trans sB q ‼ₛ ≾ₑ-refl)))
      (<:ᵛ-refl _) (·ₑ-mono sε sε₁)
      (handleⁿ nM' (λ op ε'' → rnf (hr op ε'')) nN')
      (cong₃ (λ a b d → handle a `with b `in d) eM
             (fun-ext (λ op → fun-ext (λ ε'' → rer (hr op ε'')))) eN)
  where
    hr : (op : Op) → (ε'' : E) → NfResC _ _
    hr op ε'' =
      C-subCtx (≼-∷ (≼-∷ (≼-⟨⟩ c ≾ᵣ-refl) (<:ᵛ-refl _)) (<:ᵛ-refl _)) (nH op ε'')
C-subCtx c (unboxⁿ {x = x} {rel = rel} nN) with ≼ᶜ-lookup c x
... | lkp y ([ g ]ₛ sp) b e with C-subCtx (≼-∷ c sp) nN
...   | nfc N' sv se nN' eN =
  nfc (unbox y (≾ᵣ-trans b (≾ᵣ-trans rel g)) (<:ᵛ-refl _) N') sv se
      (unboxⁿ nN') (cong₂ unbox e eN)
C-subCtx c (boxⁿ nV nN) with V-subCtx (≼-⟨⟩ c ≾ᵣ-refl) nV
... | nfv V' s nV' eV with C-subCtx (≼-∷ c ([ ≾ᵣ-refl ]ₛ s)) nN
...   | nfc N' sv se nN' eN =
  nfc (box _ V' N') sv se (boxⁿ nV' nN') (cong₂ (box _) eV eN)


-- Normalisation: every derivation has a normal one at a subtype, with the
-- same erasure.

V-normalise : ∀ {Γ A} → (V : Γ ⊢V⦂ A) → NfResV Γ V
C-normalise : ∀ {Γ A ε} → (M : Γ ⊢C⦂ A ‼ ε) → NfResC Γ M

V-normalise (var f x) =
  nfv (var f x) (<:ᵛ-refl _) varⁿ refl
V-normalise (const b) =
  nfv (const b) (<:ᵛ-refl _) constⁿ refl
V-normalise ⋆ =
  nfv ⋆ Unitₛ ⋆ⁿ refl
V-normalise true =
  nfv true Boolₛ trueⁿ refl
V-normalise false =
  nfv false Boolₛ falseⁿ refl
V-normalise zero =
  nfv zero Natₛ zeroⁿ refl
V-normalise (succ V) with V-normalise V
... | nfv V' Natₛ n e =
  nfv (succ V') Natₛ (succⁿ n) (cong succ e)
V-normalise ⦉ V , W ⦊ with V-normalise V | V-normalise W
... | nfv V' s₁ n₁ e₁ | nfv W' s₂ n₂ e₂ =
  nfv ⦉ V' , W' ⦊ (s₁ |×|ₛ s₂) (pairⁿ n₁ n₂) (cong₂ ⦉_,_⦊ e₁ e₂)
V-normalise (inl V) with V-normalise V
... | nfv V' s n e =
  nfv (inl V') (s |+|ₛ <:ᵛ-refl _) (inlⁿ n) (cong inl e)
V-normalise (inr V) with V-normalise V
... | nfv V' s n e =
  nfv (inr V') (<:ᵛ-refl _ |+|ₛ s) (inrⁿ n) (cong inr e)
V-normalise nil =
  nfv nil (<:ᵛ-refl _) nilⁿ refl
V-normalise (cons V W) with V-normalise V | V-normalise W
... | nfv V' s₁ n₁ e₁ | nfv W' s₂ n₂ e₂ =
  nfv (cons (subV V' s₁) (subV W' s₂)) (<:ᵛ-refl _) (consⁿ n₁ n₂) (cong₂ cons e₁ e₂)
V-normalise (lam {A = A} {C = B ‼ ε} M) with C-normalise M
... | nfc M' sv se n e =
  nfv (lam M') (<:ᵛ-refl A ⇒ₛ (sv ‼ₛ se)) (lamⁿ n) (cong lam e)
V-normalise (subV V p) with V-normalise V
... | nfv V' s n e =
  nfv V' (<:ᵛ-trans s p) n e

C-normalise (return V) with V-normalise V
... | nfv V' s n e =
  nfc (return V') s ≾ₑ-refl (returnⁿ n) (cong return e)
C-normalise (M ⨟ N) with C-normalise M
... | nfc M' sA sε nM eM with C-normalise N
...   | nfc N₁ sB sε' nN eN
        with C-subCtx (≼-∷ (≼-⟨⟩ (≼ᶜ-refl _) (map-monotoneᵉ sε)) sA) nN
...     | nfc N' sB' sε'' nN' eN' =
  nfc (M' ⨟ N') (<:ᵛ-trans sB' sB) (·ₑ-mono sε (≾ₑ-trans sε'' sε'))
      (seqⁿ nM nN') (cong₂ _⨟_ eM (trans eN' eN))
C-normalise (V · W) with V-normalise V
... | nfv V' (sd ⇒ₛ (sv ‼ₛ se)) nV eV with V-normalise W
...   | nfv W' sw nW eW =
  nfc (V' · subV W' (<:ᵛ-trans sw sd)) sv se (appⁿ nV nW) (cong₂ _·_ eV eW)
C-normalise (match V `in N) with V-normalise V
... | nfv V' (s₁ |×|ₛ s₂) nV eV with C-normalise N
...   | nfc N₁ sv se nN eN
        with C-subCtx (≼-∷ (≼-∷ (≼ᶜ-refl _) s₁) s₂) nN
...     | nfc N' sv' se' nN' eN' =
  nfc (match V' `in N') (<:ᵛ-trans sv' sv) (≾ₑ-trans se' se)
      (matchⁿ nV nN') (cong₂ match_`in_ eV (trans eN' eN))
C-normalise (absurd V) with V-normalise V
... | nfv V' Emptyₛ nV eV =
  nfc (absurd V') (<:ᵛ-refl _) ≾ₑ-refl (absurdⁿ nV) (cong absurd eV)
C-normalise (cmp ⋈ V W et) with V-normalise V | V-normalise W
... | nfv V' s₁ n₁ e₁ | nfv W' s₂ n₂ e₂ =
  nfc (cmp ⋈ (subV V' s₁) (subV W' s₂) et) (<:ᵛ-refl _) ≾ₑ-refl (cmpⁿ n₁ n₂)
      (cong₂ (cmp ⋈) e₁ e₂)
C-normalise (if V `then M `else N) with V-normalise V
... | nfv V' Boolₛ nV eV with C-normalise M | C-normalise N
...   | nfc M' sv₁ se₁ nM eM | nfc N' sv₂ se₂ nN eN =
  nfc (if V' `then subC M' (sv₁ ‼ₛ se₁) `else subC N' (sv₂ ‼ₛ se₂))
      (<:ᵛ-refl _) ≾ₑ-refl (ifⁿ nV nM nN)
      (cong₃ (λ a b d → if a `then b `else d) eV eM eN)
C-normalise (caseℕ V `zero M `succ N) with V-normalise V
... | nfv V' Natₛ nV eV with C-normalise M | C-normalise N
...   | nfc M' sv₁ se₁ nM eM | nfc N' sv₂ se₂ nN eN =
  nfc (caseℕ V' `zero subC M' (sv₁ ‼ₛ se₁) `succ subC N' (sv₂ ‼ₛ se₂))
      (<:ᵛ-refl _) ≾ₑ-refl (caseℕⁿ nV nM nN)
      (cong₃ (λ a b d → caseℕ a `zero b `succ d) eV eM eN)
C-normalise (recℕ V M N r) with V-normalise V
... | nfv V' Natₛ nV eV with C-normalise M | C-normalise N
...   | nfc M' sv₁ se₁ nM eM | nfc N' sv₂ se₂ nN eN =
  nfc (recℕ V' (subC M' (sv₁ ‼ₛ se₁)) (subC N' (sv₂ ‼ₛ se₂)) r)
      (<:ᵛ-refl _) ≾ₑ-refl (recℕⁿ nV nM nN)
      (cong₃ (λ a b d → recℕ a b d) eV eM eN)
C-normalise (case+ V `inl M `inr N) with V-normalise V
... | nfv V' (s₁ |+|ₛ s₂) nV eV with C-normalise M | C-normalise N
...   | nfc M₁ sv₁ se₁ nM eM | nfc N₁ sv₂ se₂ nN eN
        with C-subCtx (≼-∷ (≼ᶜ-refl _) s₁) nM | C-subCtx (≼-∷ (≼ᶜ-refl _) s₂) nN
...     | nfc M' sv₁' se₁' nM' eM' | nfc N' sv₂' se₂' nN' eN' =
  nfc (case+ V' `inl subC M' (<:ᵛ-trans sv₁' sv₁ ‼ₛ ≾ₑ-trans se₁' se₁)
                `inr subC N' (<:ᵛ-trans sv₂' sv₂ ‼ₛ ≾ₑ-trans se₂' se₂))
      (<:ᵛ-refl _) ≾ₑ-refl (case+ⁿ nV nM' nN')
      (cong₃ (λ a b d → case+ a `inl b `inr d) eV (trans eM' eM) (trans eN' eN))
C-normalise (caseL V `nil M `cons N) with V-normalise V
... | nfv V' (|List|ₛ s) nV eV with C-normalise M | C-normalise N
...   | nfc M' sv₁ se₁ nM eM | nfc N₁ sv₂ se₂ nN eN
        with C-subCtx (≼-∷ (≼-∷ (≼ᶜ-refl _) s) (|List|ₛ s)) nN
...     | nfc N' sv₂' se₂' nN' eN' =
  nfc (caseL V' `nil subC M' (sv₁ ‼ₛ se₁)
                `cons subC N' (<:ᵛ-trans sv₂' sv₂ ‼ₛ ≾ₑ-trans se₂' se₂))
      (<:ᵛ-refl _) ≾ₑ-refl (caseLⁿ nV nM nN')
      (cong₃ (λ a b d → caseL a `nil b `cons d) eV eM (trans eN' eN))
C-normalise (recL {B = B} V M N r) with V-normalise V
... | nfv V' (|List|ₛ s) nV eV with C-normalise M | C-normalise N
...   | nfc M' sv₁ se₁ nM eM | nfc N₁ sv₂ se₂ nN eN
        with C-subCtx (≼-∷ (≼-⟨⟩ (≼-∷ (≼-∷ (≼-⟨⟩ (≼ᶜ-refl _) ≾ᵣ-refl) s) (|List|ₛ s))
                                 ≾ᵣ-refl) (<:ᵛ-refl B)) nN
...     | nfc N' sv₂' se₂' nN' eN' =
  nfc (recL V' (subC M' (sv₁ ‼ₛ se₁)) (subC N' (<:ᵛ-trans sv₂' sv₂ ‼ₛ ≾ₑ-trans se₂' se₂)) r)
      (<:ᵛ-refl _) ≾ₑ-refl (recLⁿ nV nM nN')
      (cong₃ (λ a b d → recL a b d) eV eM (trans eN' eN))
C-normalise (perform op V M) with V-normalise V
... | nfv V' s nV eV with C-normalise M
...   | nfc M' sv se nM eM =
  nfc (perform op (subV V' s) M') sv (·ₑ-monoʳ-≾ₑ se)
      (performⁿ nV nM) (cong₂ (perform op) eV eM)
C-normalise (delay τ M) with C-normalise M
... | nfc M' sv se nM eM =
  nfc (delay τ M') sv (·ₑ-monoʳ-≾ₑ se) (delayⁿ nM) (cong (delay τ) eM)
C-normalise (handle_`with_`in M H N) with C-normalise M
... | nfc M' sA sε nM eM with C-normalise N
...   | nfc N₁ sB sε₁ nN eN
        with C-subCtx (≼-∷ (≼-⟨⟩ (≼ᶜ-refl _) (map-monotoneᵉ sε)) sA) nN
...     | nfc N' sB' sε₂ nN' eN' =
  nfc (handle M' `with (λ op ε'' →
         subC (rtm (hr op ε''))
              (rsubv (hr op ε'') ‼ₛ rsube (hr op ε'')))
                 `in (subC N' (<:ᵛ-trans sB' sB ‼ₛ ≾ₑ-refl)))
      (<:ᵛ-refl _) (·ₑ-mono sε (≾ₑ-trans sε₂ sε₁))
      (handleⁿ nM (λ op ε'' → rnf (hr op ε'')) nN')
      (cong₃ (λ a b d → handle a `with b `in d) eM
             (fun-ext (λ op → fun-ext (λ ε'' → rer (hr op ε''))))
             (trans eN' eN))
  where
    hr : (op : Op) → (ε'' : E) → NfResC _ _
    hr op ε'' = C-normalise (H op ε'')
C-normalise (unbox x rel p N) with C-normalise N
... | nfc N₁ sv se nN eN with C-subCtx (≼-∷ (≼ᶜ-refl _) p) nN
...   | nfc N' sv' se' nN' eN' =
  nfc (unbox x rel (<:ᵛ-refl _) N') (<:ᵛ-trans sv' sv) (≾ₑ-trans se' se)
      (unboxⁿ nN') (cong (unbox (var-pos x)) (trans eN' eN))
C-normalise (box _ V N) with V-normalise V
... | nfv V' s nV eV with C-normalise N
...   | nfc N₁ sv se nN eN with C-subCtx (≼-∷ (≼ᶜ-refl _) ([ ≾ᵣ-refl ]ₛ s)) nN
...     | nfc N' sv' se' nN' eN' =
  nfc (box _ V' N') (<:ᵛ-trans sv' sv) (≾ₑ-trans se' se)
      (boxⁿ nV nN') (cong₂ (box _) eV (trans eN' eN))
C-normalise (subC M (pv ‼ₛ pe)) with C-normalise M
... | nfc M' sv se n e =
  nfc M' (<:ᵛ-trans sv pv) (≾ₑ-trans se pe) n e


-- The theorem: every derivation equals, up to erasure, one in which every
-- subsumption sits at a reconciliation point — the root among them.

data NfRootV : ∀ {Γ A} → Γ ⊢V⦂ A → Set where
  rootⁿ : ∀ {Γ A A'} {V : Γ ⊢V⦂ A} {p : A <:ᵛ A'} → NfV V → NfRootV (subV V p)

data NfRootC : ∀ {Γ A ε} → Γ ⊢C⦂ A ‼ ε → Set where
  rootⁿ : ∀ {Γ A ε A' ε'} {M : Γ ⊢C⦂ A ‼ ε} {p : (A ‼ ε) <:ᶜ (A' ‼ ε')}
        → NfC M → NfRootC (subC M p)

V-normal-form : ∀ {Γ A} → (V : Γ ⊢V⦂ A)
              → Σ[ V' ∈ Γ ⊢V⦂ A ] NfRootV V' × (⌊ V' ⌋ᵛ ≡ ⌊ V ⌋ᵛ)
V-normal-form V with V-normalise V
... | nfv V' s n e = subV V' s , rootⁿ n , e

C-normal-form : ∀ {Γ A ε} → (M : Γ ⊢C⦂ A ‼ ε)
              → Σ[ M' ∈ Γ ⊢C⦂ A ‼ ε ] NfRootC M' × (⌊ M' ⌋ᶜ ≡ ⌊ M ⌋ᶜ)
C-normal-form M with C-normalise M
... | nfc M' sv se n e = subC M' (sv ‼ₛ se) , rootⁿ n , e


-- Sanity checks: normalisation strips the subsumptions it can.

private

  ex-strip : ∀ {Γ} → rtm (V-normalise {Γ} (subV ⋆ Unitₛ)) ≡ ⋆
  ex-strip = refl

  ex-body : ∀ {Γ A}
          → rtm (V-normalise {Γ}
                   (lam (subC (return {A = A} (var (λ _ → ≾ᵣ-refl) Hd))
                              (<:ᶜ-refl (A ‼ uₑ)))))
          ≡ lam (return (var (λ _ → ≾ᵣ-refl) Hd))
  ex-body = refl
