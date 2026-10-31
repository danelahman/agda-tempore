-------------------------------------------------------------------------
-- Subsumption is confined to the reconciliation points.               --
--                                                                     --
-- Every derivation has one with the same erasure in which `subV` and  --
-- `subC` occur only where a sub-derivation must meet a type it does   --
-- not itself determine: an application's argument, a `perform`'s      --
-- parameter, the head and tail of a `cons`, the operands of a `cmp`,  --
-- the branches of `if`, `matchℕ`, `match+` and `matchL`, the base and --
-- step of `recℕ` and `recL`, a handler's clauses and its return       --
-- clause, the handler of a `handle`, and the root.                    --
-- `NfV`/`NfC` pin those positions and `C-normal-form` is the theorem. --
--                                                                     --
-- The tool is context subsumption along `_≼ᶜ_`, which lowers binder   --
-- types and lock grades at once. It is a statement about derivations: --
-- nothing in the substitution calculus may call it, since it rebuilds --
-- every variable.                                                     --
-------------------------------------------------------------------------

open import Data.Product

open import Relation.Nullary using (¬_)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.Syntax.Normalisation (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts S
open import MonomorphicCalculus.Syntax.Erasure  S
open import MonomorphicCalculus.Syntax.Terms    S
open import MonomorphicCalculus.Syntax.Types    S

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

data NfV : ∀ {Γ A} → Γ ⊢ᵛ⦂ A → Set
data NfC : ∀ {Γ A ε} → Γ ⊢ᶜ⦂ A ! ε → Set

data NfV where

  varⁿ   : ∀ {Γ A ρ} .{f : A Et∨≾ᵘ ρ} {x : A ∈[ ρ ] Γ}
         → NfV (var x f)

  constⁿ : ∀ {Γ B} {c : BaseConstants B} → NfV {Γ} (const B c)

  ⋆ⁿ     : ∀ {Γ} → NfV {Γ} ⋆

  trueⁿ  : ∀ {Γ} → NfV {Γ} true

  falseⁿ : ∀ {Γ} → NfV {Γ} false

  zeroⁿ  : ∀ {Γ} → NfV {Γ} zero

  succⁿ  : ∀ {Γ} {V : Γ ⊢ᵛ⦂ nat} → NfV V → NfV (succ V)

  pairⁿ  : ∀ {Γ A B} {V : Γ ⊢ᵛ⦂ A} {W : Γ ⊢ᵛ⦂ B}
         → NfV V → NfV W → NfV ⦉ V , W ⦊

  inlⁿ   : ∀ {Γ A B} {V : Γ ⊢ᵛ⦂ A} → NfV V → NfV (inl {B = B} V)

  inrⁿ   : ∀ {Γ A B} {V : Γ ⊢ᵛ⦂ B} → NfV V → NfV (inr {A = A} V)

  nilⁿ   : ∀ {Γ A} → NfV {Γ} (nil {A = A})

  -- the head and the tail meet at the element type

  consⁿ  : ∀ {Γ A A₁ A₂} {V : Γ ⊢ᵛ⦂ A₁} {W : Γ ⊢ᵛ⦂ A₂}
             {p : A₁ <:ᵛ A} {q : A₂ <:ᵛ list A}
         → NfV V → NfV W → NfV (cons (subV V p) (subV W q))

  funⁿ   : ∀ {Γ A B ε} {M : Γ ∷ A ⊢ᶜ⦂ B ! ε} → NfC M → NfV (fun M)

  -- the clauses and the return clause meet at the handler's result type;
  -- the clauses' effects are fixed by the rule, the return clause's is not

  handlerⁿ : ∀ {Γ A B ε ε₁ B₁}
               {Bh : Op → E → VType} {εh : Op → E → E}
               {H : (op : Op) → (ε'' : E) →
                      Γ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                        ∷ [ ∣ op-grade op ∣ᵉ ] (⌜ arity op ⌝ᵍ ⇒ B ! ε'')
                      ⊢ᶜ⦂ Bh op ε'' ! εh op ε''}
               {p : (op : Op) → (ε'' : E) →
                      (Bh op ε'' ! εh op ε'') <:ᶜ (B ! (op-grade op ·ₑ ε''))}
               {N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B₁ ! ε₁} {q : B₁ <:ᵛ B}
           → NfC N
           → ((op : Op) → (ε'' : E) → NfC (H op ε''))
           → NfV (handler (subC N (q !ₛ ≾ₑ-refl))
                          (λ op ε'' → subC (H op ε'') (p op ε'')))

data NfC where

  returnⁿ  : ∀ {Γ A} {V : Γ ⊢ᵛ⦂ A} → NfV V → NfC (return V)

  seqⁿ     : ∀ {Γ A B ε ε'} {M : Γ ⊢ᶜ⦂ A ! ε} {N : Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'}
           → NfC M → NfC N → NfC (M ⨟ N)

  -- the argument meets the domain the function fixes

  appⁿ     : ∀ {Γ A A' B ε} {V : Γ ⊢ᵛ⦂ A ⇒ B ! ε} {W : Γ ⊢ᵛ⦂ A'} {p : A' <:ᵛ A}
           → NfV V → NfV W → NfC (V · subV W p)

  matchⁿ   : ∀ {Γ A B C ε} {V : Γ ⊢ᵛ⦂ A |×| B} {N : Γ ∷ A ∷ B ⊢ᶜ⦂ C ! ε}
           → NfV V → NfC N → NfC (match V `with N)

  absurdⁿ  : ∀ {Γ A ε} {V : Γ ⊢ᵛ⦂ empty} → NfV V → NfC (absurd {C = A ! ε} V)

  -- the operands meet at the compared type

  cmpⁿ     : ∀ {Γ A A₁ A₂ ⋈} {V : Γ ⊢ᵛ⦂ A₁} {W : Γ ⊢ᵛ⦂ A₂}
               {p : A₁ <:ᵛ A} {q : A₂ <:ᵛ A} {et : Et A}
           → NfV V → NfV W → NfC (cmp ⋈ (subV V p) (subV W q) et)

  -- the branches meet at the type the `if` is used at

  ifⁿ      : ∀ {Γ A ε A₁ ε₁ A₂ ε₂} {V : Γ ⊢ᵛ⦂ bool}
               {M : Γ ⊢ᶜ⦂ A₁ ! ε₁} {N : Γ ⊢ᶜ⦂ A₂ ! ε₂}
               {p : (A₁ ! ε₁) <:ᶜ (A ! ε)} {q : (A₂ ! ε₂) <:ᶜ (A ! ε)}
           → NfV V → NfC M → NfC N
           → NfC (if V `then subC M p `else subC N q)

  -- likewise for the branches of a `matchℕ` and of a `match+`

  matchℕⁿ  : ∀ {Γ A ε A₁ ε₁ A₂ ε₂} {V : Γ ⊢ᵛ⦂ nat}
               {M : Γ ⊢ᶜ⦂ A₁ ! ε₁} {N : Γ ∷ nat ⊢ᶜ⦂ A₂ ! ε₂}
               {p : (A₁ ! ε₁) <:ᶜ (A ! ε)} {q : (A₂ ! ε₂) <:ᶜ (A ! ε)}
           → NfV V → NfC M → NfC N
           → NfC (matchℕ V `zero subC M p `succ subC N q)

  -- the base and the step meet at the recursion's type, which the step's
  -- binder fixes

  recℕⁿ    : ∀ {Γ B ε A₁ ε₁ A₂ ε₂} {V : Γ ⊢ᵛ⦂ nat}
               {M : Γ ⊢ᶜ⦂ A₁ ! ε₁} {N : (Γ ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ A₂ ! ε₂}
               {p : (A₁ ! ε₁) <:ᶜ (B ! ε)} {q : (A₂ ! ε₂) <:ᶜ (B ! ε)}
               {r : ε ·ₑ ε ≾ₑ ε}
           → NfV V → NfC M → NfC N
           → NfC (recℕ V (subC M p) (subC N q) r)

  match+ⁿ  : ∀ {Γ A B A' ε A₁ ε₁ A₂ ε₂} {V : Γ ⊢ᵛ⦂ A |+| B}
               {M : Γ ∷ A ⊢ᶜ⦂ A₁ ! ε₁} {N : Γ ∷ B ⊢ᶜ⦂ A₂ ! ε₂}
               {p : (A₁ ! ε₁) <:ᶜ (A' ! ε)} {q : (A₂ ! ε₂) <:ᶜ (A' ! ε)}
           → NfV V → NfC M → NfC N
           → NfC (match+ V `inl subC M p `inr subC N q)

  matchLⁿ  : ∀ {Γ A A' ε A₁ ε₁ A₂ ε₂} {V : Γ ⊢ᵛ⦂ list A}
               {M : Γ ⊢ᶜ⦂ A₁ ! ε₁} {N : Γ ∷ A ∷ list A ⊢ᶜ⦂ A₂ ! ε₂}
               {p : (A₁ ! ε₁) <:ᶜ (A' ! ε)} {q : (A₂ ! ε₂) <:ᶜ (A' ! ε)}
           → NfV V → NfC M → NfC N
           → NfC (matchL V `nil subC M p `cons subC N q)

  recLⁿ    : ∀ {Γ A B ε A₁ ε₁ A₂ ε₂} {V : Γ ⊢ᵛ⦂ list A}
               {M : Γ ⊢ᶜ⦂ A₁ ! ε₁}
               {N : (Γ ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ A₂ ! ε₂}
               {p : (A₁ ! ε₁) <:ᶜ (B ! ε)} {q : (A₂ ! ε₂) <:ᶜ (B ! ε)}
               {r : ε ·ₑ ε ≾ₑ ε}
           → NfV V → NfC M → NfC N
           → NfC (recL V (subC M p) (subC N q) r)

  -- the parameter meets the ground type the operation fixes; the slack is
  -- non-trivial because ground types include the box modality

  performⁿ : ∀ {Γ A ε A' op} {V : Γ ⊢ᵛ⦂ A'} {p : A' <:ᵛ ⌜ param op ⌝ᵍ}
               {M : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ A ! ε}
           → NfV V → NfC M → NfC (perform op (subV V p) M)

  delayⁿ   : ∀ {Γ A ε τ} {M : Γ ⟨ ιᵣ τ ⟩ ⊢ᶜ⦂ A ! ε} → NfC M → NfC (delay τ M)

  -- the handler meets the type of the handled computation

  handleⁿ  : ∀ {Γ A ε C B ε'} {M : Γ ⊢ᶜ⦂ A ! ε} {V : Γ ⊢ᵛ⦂ C ⇛ (B ! ε')}
               {p : (A ! ε) <:ᶜ C}
           → NfC M → NfV V → NfC (handle M `with subV V (p ⇛ₛ <:ᶜ-refl (B ! ε')))

  -- the continuation binds the payload at its declared type

  unboxⁿ   : ∀ {Γ A ε A₀ ρ₀ ρ'} {x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ} {rel : ρ' ≾ᵣ ρ₀}
               {N : Γ ∷ A₀ ⊢ᶜ⦂ A ! ε}
           → NfC N → NfC (unbox x rel (<:ᵛ-refl A₀) N)

  boxⁿ     : ∀ {Γ A ε A₁ ρ} {V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A₁} {N : Γ ∷ [ ρ ] A₁ ⊢ᶜ⦂ A ! ε}
           → NfV V → NfC N → NfC (box _ V N)


-- A normal derivation in a subtype context, with its residual subtyping
-- and the erasure it shares with the derivation it came from.

record NfResV (Γ₀ : Ctx) {Γ : Ctx} {A : VType} (V : Γ ⊢ᵛ⦂ A) : Set where
  constructor nfv
  field
    {rty} : VType
    rtm   : Γ₀ ⊢ᵛ⦂ rty
    rsub  : rty <:ᵛ A
    rnf   : NfV rtm
    rer   : ⌊ rtm ⌋ᵛ ≡ ⌊ V ⌋ᵛ

record NfResC (Γ₀ : Ctx) {Γ : Ctx} {A : VType} {ε : E} (M : Γ ⊢ᶜ⦂ A ! ε) : Set where
  constructor nfc
  field
    {rvt} : VType
    {ref} : E
    rtm   : Γ₀ ⊢ᶜ⦂ rvt ! ref
    rsubv : rvt <:ᵛ A
    rsube : ref ≾ₑ ε
    rnf   : NfC rtm
    rer   : ⌊ rtm ⌋ᶜ ≡ ⌊ M ⌋ᶜ

open NfResV
open NfResC


-- Context subsumption: a normal derivation over a context is one over
-- any context below it, at a subtype and with the same erasure.

V-subCtx : ∀ {Γ₀ Γ₁ A} → Γ₀ ≼ᶜ Γ₁ → {V : Γ₁ ⊢ᵛ⦂ A} → NfV V → NfResV Γ₀ V
C-subCtx : ∀ {Γ₀ Γ₁ A ε} → Γ₀ ≼ᶜ Γ₁ → {M : Γ₁ ⊢ᶜ⦂ A ! ε} → NfC M → NfResC Γ₀ M

V-subCtx c (varⁿ {f = f} {x = x}) with ≼ᶜ-lookup c x
... | lkp y s b e =
  nfv (var y (Et∨≾ᵘ-<: s b f))
      s varⁿ (cong var e)
V-subCtx c (constⁿ {c = b}) =
  nfv (const _ b) (<:ᵛ-refl _) constⁿ refl
V-subCtx c ⋆ⁿ =
  nfv ⋆ unitₛ ⋆ⁿ refl
V-subCtx c trueⁿ =
  nfv true boolₛ trueⁿ refl
V-subCtx c falseⁿ =
  nfv false boolₛ falseⁿ refl
V-subCtx c zeroⁿ =
  nfv zero natₛ zeroⁿ refl
V-subCtx c (succⁿ nV) with V-subCtx c nV
... | nfv V' natₛ n e =
  nfv (succ V') natₛ (succⁿ n) (cong succ e)
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
V-subCtx c (funⁿ {A = A} nM) with C-subCtx (≼-∷ c (<:ᵛ-refl A)) nM
... | nfc M' sv se n e =
  nfv (fun M') (<:ᵛ-refl A ⇒ₛ (sv !ₛ se)) (funⁿ n) (cong fun e)
V-subCtx c (handlerⁿ {A = A} {p = p} {q = q} nN nH)
  with C-subCtx (≼-∷ (≼-⟨⟩ c ≾ᵣ-refl) (<:ᵛ-refl A)) nN
... | nfc N' sB sε₁ nN' eN =
  nfv (handler (subC N' (<:ᵛ-trans sB q !ₛ ≾ₑ-refl))
               (λ op ε'' →
                  subC (rtm (hr op ε''))
                       (<:ᶜ-trans (rsubv (hr op ε'') !ₛ rsube (hr op ε'')) (p op ε''))))
      (<:ᶜ-refl _ ⇛ₛ (<:ᵛ-refl _ !ₛ sε₁))
      (handlerⁿ nN' (λ op ε'' → rnf (hr op ε'')))
      (cong₂ handler eN (fun-ext (λ op → fun-ext (λ ε'' → rer (hr op ε'')))))
  where
    hr : (op : Op) → (ε'' : E) → NfResC _ _
    hr op ε'' =
      C-subCtx (≼-∷ (≼-∷ (≼-⟨⟩ c ≾ᵣ-refl) (<:ᵛ-refl _)) (<:ᵛ-refl _)) (nH op ε'')

C-subCtx c (returnⁿ nV) with V-subCtx c nV
... | nfv V' s n e =
  nfc (return V') s ≾ₑ-refl (returnⁿ n) (cong return e)
C-subCtx c (seqⁿ nM nN) with C-subCtx c nM
... | nfc M' sA sε nM' eM with C-subCtx (≼-∷ (≼-⟨⟩ c (map-monotoneᵉ sε)) sA) nN
...   | nfc N' sB sε' nN' eN =
  nfc (M' ⨟ N') sB (·ₑ-mono sε sε') (seqⁿ nM' nN') (cong₂ _⨟_ eM eN)
C-subCtx c (appⁿ {p = p} nV nW) with V-subCtx c nV
... | nfv V' (sd ⇒ₛ (sv !ₛ se)) nV' eV with V-subCtx c nW
...   | nfv W' sw nW' eW =
  nfc (V' · subV W' (<:ᵛ-trans sw (<:ᵛ-trans p sd))) sv se
      (appⁿ nV' nW') (cong₂ _·_ eV eW)
C-subCtx c (matchⁿ nV nN) with V-subCtx c nV
... | nfv V' (s₁ |×|ₛ s₂) nV' eV with C-subCtx (≼-∷ (≼-∷ c s₁) s₂) nN
...   | nfc N' sv se nN' eN =
  nfc (match V' `with N') sv se (matchⁿ nV' nN') (cong₂ match_`with_ eV eN)
C-subCtx c (absurdⁿ nV) with V-subCtx c nV
... | nfv V' emptyₛ nV' eV =
  nfc (absurd V') (<:ᵛ-refl _) ≾ₑ-refl (absurdⁿ nV') (cong absurd eV)
C-subCtx c (cmpⁿ {⋈ = ⋈} {p = p} {q = q} {et = et} nV nW)
  with V-subCtx c nV | V-subCtx c nW
... | nfv V' s₁ n₁ e₁ | nfv W' s₂ n₂ e₂ =
  nfc (cmp ⋈ (subV V' (<:ᵛ-trans s₁ p)) (subV W' (<:ᵛ-trans s₂ q)) et) (<:ᵛ-refl _)
      ≾ₑ-refl (cmpⁿ n₁ n₂) (cong₂ (cmp ⋈) e₁ e₂)
C-subCtx c (ifⁿ {p = p} {q = q} nV nM nN) with V-subCtx c nV
... | nfv V' boolₛ nV' eV with C-subCtx c nM | C-subCtx c nN
...   | nfc M' sv₁ se₁ nM' eM | nfc N' sv₂ se₂ nN' eN =
  nfc (if V' `then subC M' (<:ᶜ-trans (sv₁ !ₛ se₁) p)
             `else subC N' (<:ᶜ-trans (sv₂ !ₛ se₂) q))
      (<:ᵛ-refl _) ≾ₑ-refl (ifⁿ nV' nM' nN')
      (cong₃ (λ a b d → if a `then b `else d) eV eM eN)
C-subCtx c (matchℕⁿ {p = p} {q = q} nV nM nN) with V-subCtx c nV
... | nfv V' natₛ nV' eV with C-subCtx c nM | C-subCtx (≼-∷ c natₛ) nN
...   | nfc M' sv₁ se₁ nM' eM | nfc N' sv₂ se₂ nN' eN =
  nfc (matchℕ V' `zero subC M' (<:ᶜ-trans (sv₁ !ₛ se₁) p)
                 `succ subC N' (<:ᶜ-trans (sv₂ !ₛ se₂) q))
      (<:ᵛ-refl _) ≾ₑ-refl (matchℕⁿ nV' nM' nN')
      (cong₃ (λ a b d → matchℕ a `zero b `succ d) eV eM eN)
C-subCtx c (recℕⁿ {B = B} {p = p} {q = q} {r = r} nV nM nN) with V-subCtx c nV
... | nfv V' natₛ nV' eV
      with C-subCtx c nM
         | C-subCtx (≼-∷ (≼-⟨⟩ (≼-∷ (≼-⟨⟩ c ≾ᵣ-refl) natₛ) ≾ᵣ-refl) (<:ᵛ-refl B)) nN
...   | nfc M' sv₁ se₁ nM' eM | nfc N' sv₂ se₂ nN' eN =
  nfc (recℕ V' (subC M' (<:ᶜ-trans (sv₁ !ₛ se₁) p))
               (subC N' (<:ᶜ-trans (sv₂ !ₛ se₂) q)) r)
      (<:ᵛ-refl _) ≾ₑ-refl (recℕⁿ nV' nM' nN')
      (cong₃ (λ a b d → recℕ a b d) eV eM eN)
C-subCtx c (match+ⁿ {p = p} {q = q} nV nM nN) with V-subCtx c nV
... | nfv V' (s₁ |+|ₛ s₂) nV' eV
      with C-subCtx (≼-∷ c s₁) nM | C-subCtx (≼-∷ c s₂) nN
...   | nfc M' sv₁ se₁ nM' eM | nfc N' sv₂ se₂ nN' eN =
  nfc (match+ V' `inl subC M' (<:ᶜ-trans (sv₁ !ₛ se₁) p)
                 `inr subC N' (<:ᶜ-trans (sv₂ !ₛ se₂) q))
      (<:ᵛ-refl _) ≾ₑ-refl (match+ⁿ nV' nM' nN')
      (cong₃ (λ a b d → match+ a `inl b `inr d) eV eM eN)
C-subCtx c (matchLⁿ {p = p} {q = q} nV nM nN) with V-subCtx c nV
... | nfv V' (listₛ s) nV' eV
      with C-subCtx c nM | C-subCtx (≼-∷ (≼-∷ c s) (listₛ s)) nN
...   | nfc M' sv₁ se₁ nM' eM | nfc N' sv₂ se₂ nN' eN =
  nfc (matchL V' `nil subC M' (<:ᶜ-trans (sv₁ !ₛ se₁) p)
                 `cons subC N' (<:ᶜ-trans (sv₂ !ₛ se₂) q))
      (<:ᵛ-refl _) ≾ₑ-refl (matchLⁿ nV' nM' nN')
      (cong₃ (λ a b d → matchL a `nil b `cons d) eV eM eN)
C-subCtx c (recLⁿ {B = B} {p = p} {q = q} {r = r} nV nM nN) with V-subCtx c nV
... | nfv V' (listₛ s) nV' eV
      with C-subCtx c nM
         | C-subCtx (≼-∷ (≼-⟨⟩ (≼-∷ (≼-∷ (≼-⟨⟩ c ≾ᵣ-refl) s) (listₛ s)) ≾ᵣ-refl)
                         (<:ᵛ-refl B)) nN
...   | nfc M' sv₁ se₁ nM' eM | nfc N' sv₂ se₂ nN' eN =
  nfc (recL V' (subC M' (<:ᶜ-trans (sv₁ !ₛ se₁) p))
               (subC N' (<:ᶜ-trans (sv₂ !ₛ se₂) q)) r)
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
C-subCtx c (handleⁿ {p = p} nM nV) with C-subCtx c nM | V-subCtx c nV
... | nfc M' sA sε nM' eM | nfv V' (sC ⇛ₛ (sB !ₛ sε')) nV' eV =
  nfc (handle M' `with subV V' (<:ᶜ-trans (sA !ₛ sε) (<:ᶜ-trans p sC) ⇛ₛ <:ᶜ-refl _))
      sB (·ₑ-mono sε sε') (handleⁿ nM' nV') (cong₂ handle_`with_ eM eV)
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

V-normalise : ∀ {Γ A} → (V : Γ ⊢ᵛ⦂ A) → NfResV Γ V
C-normalise : ∀ {Γ A ε} → (M : Γ ⊢ᶜ⦂ A ! ε) → NfResC Γ M

V-normalise (var x f) =
  nfv (var x f) (<:ᵛ-refl _) varⁿ refl
V-normalise (const B b) =
  nfv (const B b) (<:ᵛ-refl _) constⁿ refl
V-normalise ⋆ =
  nfv ⋆ unitₛ ⋆ⁿ refl
V-normalise true =
  nfv true boolₛ trueⁿ refl
V-normalise false =
  nfv false boolₛ falseⁿ refl
V-normalise zero =
  nfv zero natₛ zeroⁿ refl
V-normalise (succ V) with V-normalise V
... | nfv V' natₛ n e =
  nfv (succ V') natₛ (succⁿ n) (cong succ e)
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
V-normalise (fun {A = A} {C = B ! ε} M) with C-normalise M
... | nfc M' sv se n e =
  nfv (fun M') (<:ᵛ-refl A ⇒ₛ (sv !ₛ se)) (funⁿ n) (cong fun e)
V-normalise (handler N H) with C-normalise N
... | nfc N' sB sε₁ nN eN =
  nfv (handler (subC N' (sB !ₛ ≾ₑ-refl))
               (λ op ε'' → subC (rtm (hr op ε'')) (rsubv (hr op ε'') !ₛ rsube (hr op ε''))))
      (<:ᶜ-refl _ ⇛ₛ (<:ᵛ-refl _ !ₛ sε₁))
      (handlerⁿ nN (λ op ε'' → rnf (hr op ε'')))
      (cong₂ handler eN (fun-ext (λ op → fun-ext (λ ε'' → rer (hr op ε'')))))
  where
    hr : (op : Op) → (ε'' : E) → NfResC _ _
    hr op ε'' = C-normalise (H op ε'')
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
... | nfv V' (sd ⇒ₛ (sv !ₛ se)) nV eV with V-normalise W
...   | nfv W' sw nW eW =
  nfc (V' · subV W' (<:ᵛ-trans sw sd)) sv se (appⁿ nV nW) (cong₂ _·_ eV eW)
C-normalise (match V `with N) with V-normalise V
... | nfv V' (s₁ |×|ₛ s₂) nV eV with C-normalise N
...   | nfc N₁ sv se nN eN
        with C-subCtx (≼-∷ (≼-∷ (≼ᶜ-refl _) s₁) s₂) nN
...     | nfc N' sv' se' nN' eN' =
  nfc (match V' `with N') (<:ᵛ-trans sv' sv) (≾ₑ-trans se' se)
      (matchⁿ nV nN') (cong₂ match_`with_ eV (trans eN' eN))
C-normalise (absurd V) with V-normalise V
... | nfv V' emptyₛ nV eV =
  nfc (absurd V') (<:ᵛ-refl _) ≾ₑ-refl (absurdⁿ nV) (cong absurd eV)
C-normalise (cmp ⋈ V W et) with V-normalise V | V-normalise W
... | nfv V' s₁ n₁ e₁ | nfv W' s₂ n₂ e₂ =
  nfc (cmp ⋈ (subV V' s₁) (subV W' s₂) et) (<:ᵛ-refl _) ≾ₑ-refl (cmpⁿ n₁ n₂)
      (cong₂ (cmp ⋈) e₁ e₂)
C-normalise (if V `then M `else N) with V-normalise V
... | nfv V' boolₛ nV eV with C-normalise M | C-normalise N
...   | nfc M' sv₁ se₁ nM eM | nfc N' sv₂ se₂ nN eN =
  nfc (if V' `then subC M' (sv₁ !ₛ se₁) `else subC N' (sv₂ !ₛ se₂))
      (<:ᵛ-refl _) ≾ₑ-refl (ifⁿ nV nM nN)
      (cong₃ (λ a b d → if a `then b `else d) eV eM eN)
C-normalise (matchℕ V `zero M `succ N) with V-normalise V
... | nfv V' natₛ nV eV with C-normalise M | C-normalise N
...   | nfc M' sv₁ se₁ nM eM | nfc N' sv₂ se₂ nN eN =
  nfc (matchℕ V' `zero subC M' (sv₁ !ₛ se₁) `succ subC N' (sv₂ !ₛ se₂))
      (<:ᵛ-refl _) ≾ₑ-refl (matchℕⁿ nV nM nN)
      (cong₃ (λ a b d → matchℕ a `zero b `succ d) eV eM eN)
C-normalise (recℕ V M N r) with V-normalise V
... | nfv V' natₛ nV eV with C-normalise M | C-normalise N
...   | nfc M' sv₁ se₁ nM eM | nfc N' sv₂ se₂ nN eN =
  nfc (recℕ V' (subC M' (sv₁ !ₛ se₁)) (subC N' (sv₂ !ₛ se₂)) r)
      (<:ᵛ-refl _) ≾ₑ-refl (recℕⁿ nV nM nN)
      (cong₃ (λ a b d → recℕ a b d) eV eM eN)
C-normalise (match+ V `inl M `inr N) with V-normalise V
... | nfv V' (s₁ |+|ₛ s₂) nV eV with C-normalise M | C-normalise N
...   | nfc M₁ sv₁ se₁ nM eM | nfc N₁ sv₂ se₂ nN eN
        with C-subCtx (≼-∷ (≼ᶜ-refl _) s₁) nM | C-subCtx (≼-∷ (≼ᶜ-refl _) s₂) nN
...     | nfc M' sv₁' se₁' nM' eM' | nfc N' sv₂' se₂' nN' eN' =
  nfc (match+ V' `inl subC M' (<:ᵛ-trans sv₁' sv₁ !ₛ ≾ₑ-trans se₁' se₁)
                 `inr subC N' (<:ᵛ-trans sv₂' sv₂ !ₛ ≾ₑ-trans se₂' se₂))
      (<:ᵛ-refl _) ≾ₑ-refl (match+ⁿ nV nM' nN')
      (cong₃ (λ a b d → match+ a `inl b `inr d) eV (trans eM' eM) (trans eN' eN))
C-normalise (matchL V `nil M `cons N) with V-normalise V
... | nfv V' (listₛ s) nV eV with C-normalise M | C-normalise N
...   | nfc M' sv₁ se₁ nM eM | nfc N₁ sv₂ se₂ nN eN
        with C-subCtx (≼-∷ (≼-∷ (≼ᶜ-refl _) s) (listₛ s)) nN
...     | nfc N' sv₂' se₂' nN' eN' =
  nfc (matchL V' `nil subC M' (sv₁ !ₛ se₁)
                 `cons subC N' (<:ᵛ-trans sv₂' sv₂ !ₛ ≾ₑ-trans se₂' se₂))
      (<:ᵛ-refl _) ≾ₑ-refl (matchLⁿ nV nM nN')
      (cong₃ (λ a b d → matchL a `nil b `cons d) eV eM (trans eN' eN))
C-normalise (recL {B = B} V M N r) with V-normalise V
... | nfv V' (listₛ s) nV eV with C-normalise M | C-normalise N
...   | nfc M' sv₁ se₁ nM eM | nfc N₁ sv₂ se₂ nN eN
        with C-subCtx (≼-∷ (≼-⟨⟩ (≼-∷ (≼-∷ (≼-⟨⟩ (≼ᶜ-refl _) ≾ᵣ-refl) s) (listₛ s))
                                 ≾ᵣ-refl) (<:ᵛ-refl B)) nN
...     | nfc N' sv₂' se₂' nN' eN' =
  nfc (recL V' (subC M' (sv₁ !ₛ se₁)) (subC N' (<:ᵛ-trans sv₂' sv₂ !ₛ ≾ₑ-trans se₂' se₂)) r)
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
C-normalise (handle M `with V) with C-normalise M | V-normalise V
... | nfc M' sA sε nM eM | nfv V' (sC ⇛ₛ (sB !ₛ sε')) nV eV =
  nfc (handle M' `with subV V' (<:ᶜ-trans (sA !ₛ sε) sC ⇛ₛ <:ᶜ-refl _))
      sB (·ₑ-mono sε sε') (handleⁿ nM nV) (cong₂ handle_`with_ eM eV)
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
C-normalise (subC M (pv !ₛ pe)) with C-normalise M
... | nfc M' sv se n e =
  nfc M' (<:ᵛ-trans sv pv) (≾ₑ-trans se pe) n e


-- Every derivation equals, up to erasure, one in which every subsumption sits
-- at a reconciliation point, the root among them.

data NfRootV : ∀ {Γ A} → Γ ⊢ᵛ⦂ A → Set where
  rootⁿ : ∀ {Γ A A'} {V : Γ ⊢ᵛ⦂ A} {p : A <:ᵛ A'} → NfV V → NfRootV (subV V p)

data NfRootC : ∀ {Γ A ε} → Γ ⊢ᶜ⦂ A ! ε → Set where
  rootⁿ : ∀ {Γ A ε A' ε'} {M : Γ ⊢ᶜ⦂ A ! ε} {p : (A ! ε) <:ᶜ (A' ! ε')}
        → NfC M → NfRootC (subC M p)

V-normal-form : ∀ {Γ A} → (V : Γ ⊢ᵛ⦂ A)
              → Σ[ V' ∈ Γ ⊢ᵛ⦂ A ] NfRootV V' × (⌊ V' ⌋ᵛ ≡ ⌊ V ⌋ᵛ)
V-normal-form V with V-normalise V
... | nfv V' s n e = subV V' s , rootⁿ n , e

C-normal-form : ∀ {Γ A ε} → (M : Γ ⊢ᶜ⦂ A ! ε)
              → Σ[ M' ∈ Γ ⊢ᶜ⦂ A ! ε ] NfRootC M' × (⌊ M' ⌋ᶜ ≡ ⌊ M ⌋ᶜ)
C-normal-form M with C-normalise M
... | nfc M' sv se n e = subC M' (sv !ₛ se) , rootⁿ n , e


-- Sanity checks: normalisation strips the subsumptions it can.

private

  ex-strip : ∀ {Γ} → rtm (V-normalise {Γ} (subV ⋆ unitₛ)) ≡ ⋆
  ex-strip = refl

  ex-body : ∀ {Γ A}
          → rtm (V-normalise {Γ}
                   (fun (subC (return {A = A} (var Hd (≾ᵘ-ok ≾ᵣ-refl)))
                              (<:ᶜ-refl (A ! 𝟏ₑ)))))
          ≡ fun (return (var Hd (≾ᵘ-ok ≾ᵣ-refl)))
  ex-body = refl
