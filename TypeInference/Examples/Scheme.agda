------------------------------------------------------------------
-- What inference reports, and notation for writing it          --
--                                                              --
-- `scheme` projects a `typed` verdict onto its scheme          --
-- `∀ Θ̃. Q̃ ∧ R̃ ⇒ X̃`: the scope, the hypotheses, the obligations --
-- and the type. `IsTyped` holds exactly of a `typed` verdict.  --
--                                                              --
-- `scheme` returns its scheme fully evaluated (see `walk`); a  --
-- `refl` check against a literal runs the solver once.         --
--                                                              --
-- Notation: `∀[ a , b , c ] C ⟹ X` is a scheme over `a` type,  --
-- `b` resource-grade and `c` effect-grade variables, `C` a     --
-- conjunction `_∧_` of atoms (`⊤` the empty one), and          --
-- `∀[ a , b , c ] C & R ⟹ X` one with obligations `R`.         --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹; _∧_ to _&&_)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using () renaming (⊤ to 𝟙)

open import Relation.Nullary.Decidable using (does)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import TypeInference.Scopes

module TypeInference.Examples.Scheme (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades using (_≡ᵣ?_; _≡ₑ?_)
open Operations Ops using (Op)

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S using (OCtx)
open import TypeInference.OpenSyntax.Hyps      S using (Hyps; hyps; ets; subᵥ; ordᵣ; ordₑ; disj)
open import TypeInference.OpenSyntax.Instances S using (Oblig; Obligs; oblig; _+eⁿ_)
open import TypeInference.Raw.Syntax           S
open import TypeInference.Principality         S

------------------------------------------------------------------
-- Schemes

-- A scheme: its scope, hypotheses, obligations and type

Scheme : Set
Scheme = Σ Scope (λ Θ → Hyps Θ × Obligs Θ × OCType Θ)

-- Forcing a scheme
--
-- `walk` visits every constructor of a scheme and answers `true`, an
-- answer that is never used. Computing it evaluates the whole scheme in
-- one reduction, in which all parts share one run of the solver. A
-- grade constant is forced by the carrier's decision procedure.

private

  walkℕ : ℕ → 𝔹
  walkℕ zero    = true
  walkℕ (suc n) = walkℕ n

  walkᶠ : ∀ {n} → Fin n → 𝔹
  walkᶠ zero    = true
  walkᶠ (suc i) = walkᶠ i

  walkᵉ : ∀ {Θ} → EExp Θ → 𝔹
  walkᵉ (evar i)   = walkᶠ i
  walkᵉ (econst c) = does (c ≡ₑ? c)
  walkᵉ (ε ·̂ₑ ε')  = walkᵉ ε && walkᵉ ε'
  walkᵉ (ε ⊔̂ₑ ε')  = walkᵉ ε && walkᵉ ε'

  walkʳ : ∀ {Θ} → RExp Θ → 𝔹
  walkʳ (rvar i)   = walkᶠ i
  walkʳ (rconst c) = does (c ≡ᵣ? c)
  walkʳ (ρ ·̂ᵣ ρ')  = walkʳ ρ && walkʳ ρ'
  walkʳ (ρ ⊔̂ᵣ ρ')  = walkʳ ρ && walkʳ ρ'
  walkʳ ∣ ε ∣̂ᵉ     = walkᵉ ε

  mutual

    walkᵛ : ∀ {Θ} → OVType Θ → 𝔹
    walkᵛ (tvar α)  = walkᶠ α
    walkᵛ (Base b)  = true
    walkᵛ Unit      = true
    walkᵛ Bool      = true
    walkᵛ (A |×| B) = walkᵛ A && walkᵛ B
    walkᵛ Empty     = true
    walkᵛ (A ⇒ C)   = walkᵛ A && walkᶜ C
    walkᵛ ([ ρ ] A) = walkʳ ρ && walkᵛ A

    walkᶜ : ∀ {Θ} → OCType Θ → 𝔹
    walkᶜ (A ‼ ε) = walkᵛ A && walkᵉ ε

  walkˡ : ∀ {A : Set} → (A → 𝔹) → List A → 𝔹
  walkˡ f []       = true
  walkˡ f (x ∷ xs) = f x && walkˡ f xs

  walkᵖ : ∀ {A B : Set} → (A → 𝔹) → (B → 𝔹) → A × B → 𝔹
  walkᵖ f g (x , y) = f x && g y

  walkᴴ : ∀ {Θ} → Hyps Θ → 𝔹
  walkᴴ (hyps es ss rs fs ds) =
    walkˡ walkᶠ es && walkˡ (walkᵖ walkᶠ walkᶠ) ss
    && walkˡ (walkᵖ walkʳ walkʳ) rs && walkˡ (walkᵖ walkᵉ walkᵉ) fs
    && walkˡ (walkᵖ walkᵛ walkʳ) ds

  walk : Scheme → 𝔹
  walk (scope a b c , Q , R , X) =
    walkℕ a && walkℕ b && walkℕ c && walkᴴ Q
    && walkˡ (λ { (oblig _ k O) → walkℕ k && walkᴴ O }) R && walkᶜ X

  -- `x`, whatever `b` is; matching on `b` computes it first

  after : ∀ {A : Set} → 𝔹 → A → A
  after true  x = x
  after false x = x

  -- `just r`, with `r` evaluated in full

  scheme! : Scheme → Maybe Scheme
  scheme! r = after (walk r) (just r)

scheme : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} → Inference Γ M → Maybe Scheme
scheme (typed p) = scheme! (PrincipalTyping.Θ̃ p , PrincipalTyping.Q̃ p ,
                            PrincipalTyping.R̃ p , PrincipalTyping.X̃ p)
scheme untypable = nothing
scheme stuck     = nothing

-- A data type: stating it does not run inference

data IsTyped {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} : Inference Γ M → Set where
  is-typed : (p : PrincipalTyping Γ M) → IsTyped (typed p)

------------------------------------------------------------------
-- Schemes as a paper writes them

-- An atom of a hypothesis set, one former per field

data Atom (Θ : Scope) : Set where
  et-atom   : TyVar Θ → Atom Θ
  sub-atom  : TyVar Θ → TyVar Θ → Atom Θ
  ordʳ-atom : RExp Θ → RExp Θ → Atom Θ
  ordᵉ-atom : EExp Θ → EExp Θ → Atom Θ
  disj-atom : OVType Θ → RExp Θ → Atom Θ

-- A conjunction of atoms

Conj : Scope → Set
Conj Θ = List (Atom Θ)

infixr 4 _∧_

⊤ : ∀ {Θ} → Conj Θ
⊤ = []

_∧_ : ∀ {Θ} → Conj Θ → Conj Θ → Conj Θ
_∧_ = _++_

-- An atom's type variable is named by its type

IsTyVar : ∀ {Θ} → OVType Θ → Set
IsTyVar (tvar _) = 𝟙
IsTyVar _        = ⊥

tyvar : ∀ {Θ} → (A : OVType Θ) → IsTyVar A → TyVar Θ
tyvar (tvar α) _ = α

-- The atoms. `eternal A ∨ ρ ≾ûᵣ` is a var-rule disjunction: `A` is
-- eternal or `ρ ≾ uᵣ`.

infix 6 eternal_ _<:_ _≾ᵣ_ _≾ₑ_

eternal_ : ∀ {Θ} → (A : OVType Θ) → {IsTyVar A} → Conj Θ
(eternal A) {a} = et-atom (tyvar A a) ∷ []

_<:_ : ∀ {Θ} → (A B : OVType Θ) → {IsTyVar A} → {IsTyVar B} → Conj Θ
(A <: B) {a} {b} = sub-atom (tyvar A a) (tyvar B b) ∷ []

_≾ᵣ_ : ∀ {Θ} → RExp Θ → RExp Θ → Conj Θ
ρ ≾ᵣ ρ' = ordʳ-atom ρ ρ' ∷ []

_≾ₑ_ : ∀ {Θ} → EExp Θ → EExp Θ → Conj Θ
ε ≾ₑ ε' = ordᵉ-atom ε ε' ∷ []

eternal_∨_≾ûᵣ : ∀ {Θ} → OVType Θ → RExp Θ → Conj Θ
eternal A ∨ ρ ≾ûᵣ = disj-atom A ρ ∷ []

-- A conjunction is the hypothesis set with each atom in its field,
-- in order: an expected scheme lists each field's atoms in the order
-- the solver reports them.

hypsOf : ∀ {Θ} → Conj Θ → Hyps Θ
hypsOf []                     = hyps [] [] [] [] []
hypsOf (et-atom α      ∷ C) = let Q = hypsOf C in record Q { ets  = α ∷ ets Q }
hypsOf (sub-atom α β   ∷ C) = let Q = hypsOf C in record Q { subᵥ = (α , β) ∷ subᵥ Q }
hypsOf (ordʳ-atom ρ ρ' ∷ C) = let Q = hypsOf C in record Q { ordᵣ = (ρ , ρ') ∷ ordᵣ Q }
hypsOf (ordᵉ-atom ε ε' ∷ C) = let Q = hypsOf C in record Q { ordₑ = (ε , ε') ∷ ordₑ Q }
hypsOf (disj-atom A ρ  ∷ C) = let Q = hypsOf C in record Q { disj = (A , ρ) ∷ disj Q }

-- Obligations: `∀ᵉ k ∙ C` binds `k` rigid effect variables over `C`,
-- `∀ᵉ⟨ op ⟩ k ∙ C` is left by the clause for `op`

infix 3 ∀ᵉ_∙_ ∀ᵉ⟨_⟩_∙_

∀ᵉ_∙_ : ∀ {Θ} → (k : ℕ) → Conj (Θ +eⁿ k) → Oblig Θ
∀ᵉ k ∙ C = oblig nothing k (hypsOf C)

∀ᵉ⟨_⟩_∙_ : ∀ {Θ} → Op → (k : ℕ) → Conj (Θ +eⁿ k) → Oblig Θ
∀ᵉ⟨ op ⟩ k ∙ C = oblig (just op) k (hypsOf C)

-- Schemes: `a` type, `b` resource-grade and `c` effect-grade
-- variables, hypotheses `C`, obligations `R`, type `X`

infixr 2 ∀[_,_,_]_&_⟹_ ∀[_,_,_]_⟹_

∀[_,_,_]_&_⟹_ : (a b c : ℕ) → Conj (scope a b c) → Obligs (scope a b c)
              → OCType (scope a b c) → Scheme
∀[ a , b , c ] C & R ⟹ X = scope a b c , hypsOf C , R , X

∀[_,_,_]_⟹_ : (a b c : ℕ) → Conj (scope a b c) → OCType (scope a b c) → Scheme
∀[ a , b , c ] C ⟹ X = ∀[ a , b , c ] C & [] ⟹ X
