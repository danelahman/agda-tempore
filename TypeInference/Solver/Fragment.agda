------------------------------------------------------------------
-- Biased satisfaction, and the fragment on which it is exact    --
--                                                                --
-- `Et∨≾ᵘ` is the only constraint former whose satisfaction is a  --
-- disjunction, and `Hyps` cannot express one: neither disjunct   --
-- dominates the other, so no solution is principal among both.   --
-- Two tiers answer this.                                          --
--                                                                --
-- Tier one is `_⊨ᴿ[_]_`, satisfaction with the disjunction        --
-- resolved in favour of its grade disjunct. It is what a solver   --
-- that never constrains a type to be eternal is principal for,    --
-- and it holds for every constraint: `⊨ᴿ→⊨` is `inj₂`.            --
--                                                                --
-- Tier two is `Frag`, the class of constraints on which the bias  --
-- costs nothing: those whose `Et∨≾ᵘ` atoms carry a grade          --
-- convertible to the unit, where the grade disjunct is true       --
-- outright. The atom is raised at a use of a variable across an   --
-- accumulated lock grade, so `Frag` says: every variable is used  --
-- at unit lock grade. Lock-free programs qualify, as do uses of   --
-- a variable bound after the last former that locks; uses of an   --
-- outer variable inside a `⨟`-continuation, a `perform`, a        --
-- `delay` or a `box` body do not.                                 --
--                                                                --
-- `NoRig` is the second, orthogonal restriction, and it is a      --
-- restriction on refutation only: a rigid effect-grade binder is  --
-- where a solver must discharge, rather than carry, the atoms     --
-- mentioning the eigenvariable, and a discharge that fails is a   --
-- failure of the decision procedure, not a proof that there is    --
-- no solution.                                                    --
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.Solver.Fragment (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S
open import TypeInference.Open.Hyps   S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S
open import TypeInference.Constraints.Properties   S using (≐ˢ-,ᵗ; ≐ˢ-,ʳ; ≐ˢ-,ᵉ; ≐ˢ-↑ᵉ)

open import TypeInference.SolverImpl.Enum S using (AllOp; all-lookup; all-build)

--------------------------------------------------------------
-- Tier one: biased satisfaction                             --
--                                                           --
-- Verbatim `_⊨[_]_` except at `Et∨≾ᵘ`, where the grade       --
-- disjunct is forced.                                        --
--------------------------------------------------------------

infix 4 _⊨ᴿ[_]_

_⊨ᴿ[_]_ : ∀ {Θ Θ'} → Subst Θ Θ' → Hyps Θ' → Constraint Θ → Set
σ ⊨ᴿ[ Q ] ⊤̂                       = ⊤
σ ⊨ᴿ[ Q ] ⊥̂                       = ⊥
σ ⊨ᴿ[ Q ] (C ∧̂ D)                 = σ ⊨ᴿ[ Q ] C × σ ⊨ᴿ[ Q ] D
σ ⊨ᴿ[ Q ] (A ≐ᵥ B)                = A [ σ ]ᵛ ≡ B [ σ ]ᵛ
σ ⊨ᴿ[ Q ] (ρ ≾̂ᵣᶜ ρ')              = Q ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
σ ⊨ᴿ[ Q ] (ε ≾̂ₑᶜ ε')              = Q ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ
σ ⊨ᴿ[ Q ] Etᶜ A                   = Q ⊩ᴱ A [ σ ]ᵛ
σ ⊨ᴿ[ Q ] Et∨≾ᵘ A ρ               = Q ⊩ ρ [ σ ]ʳ ≾̂ᵣ ûᵣ
_⊨ᴿ[_]_ {Θ' = Θ'} σ Q (∃ᵗ C)      = Σ[ B ∈ OVType Θ' ] ((σ ,ᵗ B) ⊨ᴿ[ Q ] C)
_⊨ᴿ[_]_ {Θ' = Θ'} σ Q (∃ʳ C)      = Σ[ ρ ∈ RExp Θ' ]   ((σ ,ʳ ρ) ⊨ᴿ[ Q ] C)
_⊨ᴿ[_]_ {Θ' = Θ'} σ Q (∃ᵉ C)      = Σ[ ε ∈ EExp Θ' ]   ((σ ,ᵉ ε) ⊨ᴿ[ Q ] C)
σ ⊨ᴿ[ Q ] (∀ᵉ C)                  = (σ ↑ᵉ) ⊨ᴿ[ wkᵉ-H Q ] C
σ ⊨ᴿ[ Q ] ⋀ᵒᵖ f                   = (op : Op) → σ ⊨ᴿ[ Q ] f op

-- A biased solution is a solution

⊨ᴿ→⊨ : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
     → (C : Constraint Θ) → σ ⊨ᴿ[ Q ] C → σ ⊨[ Q ] C
⊨ᴿ→⊨ ⊤̂            s       = s
⊨ᴿ→⊨ ⊥̂            s       = s
⊨ᴿ→⊨ (C ∧̂ D)      (s , t) = ⊨ᴿ→⊨ C s , ⊨ᴿ→⊨ D t
⊨ᴿ→⊨ (A ≐ᵥ B)     s       = s
⊨ᴿ→⊨ (ρ ≾̂ᵣᶜ ρ')   s       = s
⊨ᴿ→⊨ (ε ≾̂ₑᶜ ε')   s       = s
⊨ᴿ→⊨ (Etᶜ A)      s       = s
⊨ᴿ→⊨ (Et∨≾ᵘ A ρ)  s       = inj₂ s
⊨ᴿ→⊨ (∃ᵗ C)       (B , s) = B , ⊨ᴿ→⊨ C s
⊨ᴿ→⊨ (∃ʳ C)       (ρ , s) = ρ , ⊨ᴿ→⊨ C s
⊨ᴿ→⊨ (∃ᵉ C)       (ε , s) = ε , ⊨ᴿ→⊨ C s
⊨ᴿ→⊨ (∀ᵉ C)       s       = ⊨ᴿ→⊨ C s
⊨ᴿ→⊨ (⋀ᵒᵖ f)      s       = λ op → ⊨ᴿ→⊨ (f op) (s op)

-- Biased satisfaction respects pointwise equality of substitutions

⊨ᴿ-resp-≐ˢ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} {Q : Hyps Θ'}
           → σ ≐ˢ σ' → (C : Constraint Θ) → σ ⊨ᴿ[ Q ] C → σ' ⊨ᴿ[ Q ] C
⊨ᴿ-resp-≐ˢ p ⊤̂                   s       = s
⊨ᴿ-resp-≐ˢ p ⊥̂                   s       = s
⊨ᴿ-resp-≐ˢ p (C ∧̂ D)             (s , t) = ⊨ᴿ-resp-≐ˢ p C s , ⊨ᴿ-resp-≐ˢ p D t
⊨ᴿ-resp-≐ˢ p (A ≐ᵥ B)            s       =
  trans (sym ([≐]ᵛ p A)) (trans s ([≐]ᵛ p B))
⊨ᴿ-resp-≐ˢ {Q = Q} p (ρ ≾̂ᵣᶜ ρ')  s       =
  subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([≐]ʳ p ρ) ([≐]ʳ p ρ') s
⊨ᴿ-resp-≐ˢ {Q = Q} p (ε ≾̂ₑᶜ ε')  s       =
  subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([≐]ᵉ p ε) ([≐]ᵉ p ε') s
⊨ᴿ-resp-≐ˢ {Q = Q} p (Etᶜ A)     s       = subst (Q ⊩ᴱ_) ([≐]ᵛ p A) s
⊨ᴿ-resp-≐ˢ {Q = Q} p (Et∨≾ᵘ A ρ) s       =
  subst (λ x → Q ⊩ x ≾̂ᵣ ûᵣ) ([≐]ʳ p ρ) s
⊨ᴿ-resp-≐ˢ p (∃ᵗ C)              (B , s) = B , ⊨ᴿ-resp-≐ˢ (≐ˢ-,ᵗ p B) C s
⊨ᴿ-resp-≐ˢ p (∃ʳ C)              (ρ , s) = ρ , ⊨ᴿ-resp-≐ˢ (≐ˢ-,ʳ p ρ) C s
⊨ᴿ-resp-≐ˢ p (∃ᵉ C)              (ε , s) = ε , ⊨ᴿ-resp-≐ˢ (≐ˢ-,ᵉ p ε) C s
⊨ᴿ-resp-≐ˢ p (∀ᵉ C)              s       = ⊨ᴿ-resp-≐ˢ (≐ˢ-↑ᵉ p) C s
⊨ᴿ-resp-≐ˢ p (⋀ᵒᵖ f)             s       = λ op → ⊨ᴿ-resp-≐ˢ p (f op) (s op)

--------------------------------------------------------------
-- Tier two: the static fragment                             --
--------------------------------------------------------------

data Frag {Θ : Scope} : Constraint Θ → Set where
  ⊤ᶠ    : Frag ⊤̂
  ⊥ᶠ    : Frag ⊥̂
  _∧ᶠ_  : ∀ {C D} → Frag C → Frag D → Frag (C ∧̂ D)
  ≐ᶠ    : ∀ {A B} → Frag (A ≐ᵥ B)
  ≾ᵣᶠ   : ∀ {ρ ρ'} → Frag (ρ ≾̂ᵣᶜ ρ')
  ≾ₑᶠ   : ∀ {ε ε'} → Frag (ε ≾̂ₑᶜ ε')
  Etᶠ   : ∀ {A} → Frag (Etᶜ A)
  Et∨ᶠ  : ∀ {A ρ} → ρ ≡̂ᵣ ûᵣ → Frag (Et∨≾ᵘ A ρ)
  ∃ᵗᶠ   : ∀ {C} → Frag C → Frag (∃ᵗ C)
  ∃ʳᶠ   : ∀ {C} → Frag C → Frag (∃ʳ C)
  ∃ᵉᶠ   : ∀ {C} → Frag C → Frag (∃ᵉ C)
  ∀ᵉᶠ   : ∀ {C} → Frag C → Frag (∀ᵉ C)
  ⋀ᶠ    : ∀ {f} → ((op : Op) → Frag (f op)) → Frag (⋀ᵒᵖ f)

infixr 6 _∧ᶠ_

-- On the fragment the bias is free

Frag-⊨→⊨ᴿ : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {C : Constraint Θ}
          → Frag C → σ ⊨[ Q ] C → σ ⊨ᴿ[ Q ] C
Frag-⊨→⊨ᴿ ⊤ᶠ            s       = s
Frag-⊨→⊨ᴿ ⊥ᶠ            s       = s
Frag-⊨→⊨ᴿ (fc ∧ᶠ fd)    (s , t) = Frag-⊨→⊨ᴿ fc s , Frag-⊨→⊨ᴿ fd t
Frag-⊨→⊨ᴿ ≐ᶠ            s       = s
Frag-⊨→⊨ᴿ ≾ᵣᶠ           s       = s
Frag-⊨→⊨ᴿ ≾ₑᶠ           s       = s
Frag-⊨→⊨ᴿ Etᶠ           s       = s
Frag-⊨→⊨ᴿ {σ = σ} (Et∨ᶠ p) s    = eqᵣ (≡̂ᵣ-subst σ p)
Frag-⊨→⊨ᴿ (∃ᵗᶠ f)       (B , s) = B , Frag-⊨→⊨ᴿ f s
Frag-⊨→⊨ᴿ (∃ʳᶠ f)       (ρ , s) = ρ , Frag-⊨→⊨ᴿ f s
Frag-⊨→⊨ᴿ (∃ᵉᶠ f)       (ε , s) = ε , Frag-⊨→⊨ᴿ f s
Frag-⊨→⊨ᴿ (∀ᵉᶠ f)       s       = Frag-⊨→⊨ᴿ f s
Frag-⊨→⊨ᴿ (⋀ᶠ f)        s       = λ op → Frag-⊨→⊨ᴿ (f op) (s op)

--------------------------------------------------------------
-- Constraints without a rigid binder                        --
--------------------------------------------------------------

data NoRig {Θ : Scope} : Constraint Θ → Set where
  ⊤ⁿ    : NoRig ⊤̂
  ⊥ⁿ    : NoRig ⊥̂
  _∧ⁿ_  : ∀ {C D} → NoRig C → NoRig D → NoRig (C ∧̂ D)
  ≐ⁿ    : ∀ {A B} → NoRig (A ≐ᵥ B)
  ≾ᵣⁿ   : ∀ {ρ ρ'} → NoRig (ρ ≾̂ᵣᶜ ρ')
  ≾ₑⁿ   : ∀ {ε ε'} → NoRig (ε ≾̂ₑᶜ ε')
  Etⁿ   : ∀ {A} → NoRig (Etᶜ A)
  Et∨ⁿ  : ∀ {A ρ} → NoRig (Et∨≾ᵘ A ρ)
  ∃ᵗⁿ   : ∀ {C} → NoRig C → NoRig (∃ᵗ C)
  ∃ʳⁿ   : ∀ {C} → NoRig C → NoRig (∃ʳ C)
  ∃ᵉⁿ   : ∀ {C} → NoRig C → NoRig (∃ᵉ C)
  ⋀ⁿ    : ∀ {f} → ((op : Op) → NoRig (f op)) → NoRig (⋀ᵒᵖ f)

infixr 6 _∧ⁿ_

--------------------------------------------------------------
-- Deciding that a grade expression is the unit              --
--                                                           --
-- The atoms of a product must all cancel; a constant must be --
-- the unit; an image is the unit exactly when its argument   --
-- is, `∣_∣̂ᵉ` being a monoid morphism.                        --
--------------------------------------------------------------

unitₑ? : ∀ {Θ} → (ε : EExp Θ) → Maybe (ε ≡̂ₑ ûₑ)
unitₑ? (evar i)   = nothing
unitₑ? (econst c) with c ≡ₑ? uₑ
... | yes refl = just ≡̂ₑ-refl
... | no _     = nothing
unitₑ? (ε ·̂ₑ ε') with unitₑ? ε | unitₑ? ε'
... | just p  | just q  = just (≡̂ₑ-trans (≡̂ₑ-cong p q) ≡̂ₑ-identityˡ)
... | _       | _       = nothing

unitᵣ? : ∀ {Θ} → (ρ : RExp Θ) → Maybe (ρ ≡̂ᵣ ûᵣ)
unitᵣ? (rvar i)   = nothing
unitᵣ? (rconst c) with c ≡ᵣ? uᵣ
... | yes refl = just ≡̂ᵣ-refl
... | no _     = nothing
unitᵣ? (ρ ·̂ᵣ ρ') with unitᵣ? ρ | unitᵣ? ρ'
... | just p  | just q  = just (≡̂ᵣ-trans (≡̂ᵣ-cong p q) ≡̂ᵣ-identityˡ)
... | _       | _       = nothing
unitᵣ? ∣ ε ∣̂ᵉ     with unitₑ? ε
... | just p  = just (≡̂ᵣ-trans (≡̂ᵣ-map-cong p)
                               (subst (λ x → ∣ ûₑ ∣̂ᵉ ≡̂ᵣ rconst x) map-uᵉ ≡̂ᵣ-map-const))
... | nothing = nothing

--------------------------------------------------------------
-- Deciding the two restrictions                             --
--                                                           --
-- `⋀ᵒᵖ` carries a function, so its clause is decided by      --
-- exhausting an enumeration of the operation symbols and     --
-- reading the result back with `all-lookup`.                 --
--------------------------------------------------------------

frag? : ∀ {Θ} → OpEnum S → (C : Constraint Θ) → Maybe (Frag C)
frag? oe ⊤̂             = just ⊤ᶠ
frag? oe ⊥̂             = just ⊥ᶠ
frag? oe (C ∧̂ D) with frag? oe C | frag? oe D
... | just p  | just q  = just (p ∧ᶠ q)
... | _       | _       = nothing
frag? oe (A ≐ᵥ B)      = just ≐ᶠ
frag? oe (ρ ≾̂ᵣᶜ ρ')    = just ≾ᵣᶠ
frag? oe (ε ≾̂ₑᶜ ε')    = just ≾ₑᶠ
frag? oe (Etᶜ A)       = just Etᶠ
frag? oe (Et∨≾ᵘ A ρ) with unitᵣ? ρ
... | just p  = just (Et∨ᶠ p)
... | nothing = nothing
frag? oe (∃ᵗ C) with frag? oe C
... | just p  = just (∃ᵗᶠ p)
... | nothing = nothing
frag? oe (∃ʳ C) with frag? oe C
... | just p  = just (∃ʳᶠ p)
... | nothing = nothing
frag? oe (∃ᵉ C) with frag? oe C
... | just p  = just (∃ᵉᶠ p)
... | nothing = nothing
frag? oe (∀ᵉ C) with frag? oe C
... | just p  = just (∀ᵉᶠ p)
... | nothing = nothing
frag? oe (⋀ᵒᵖ f) with all-build (λ op → frag? oe (f op)) (OpEnum.ops oe)
... | just ps = just (⋀ᶠ (λ op → all-lookup ps (OpEnum.complete oe op)))
... | nothing = nothing

norig? : ∀ {Θ} → OpEnum S → (C : Constraint Θ) → Maybe (NoRig C)
norig? oe ⊤̂            = just ⊤ⁿ
norig? oe ⊥̂            = just ⊥ⁿ
norig? oe (C ∧̂ D) with norig? oe C | norig? oe D
... | just p  | just q  = just (p ∧ⁿ q)
... | _       | _       = nothing
norig? oe (A ≐ᵥ B)     = just ≐ⁿ
norig? oe (ρ ≾̂ᵣᶜ ρ')   = just ≾ᵣⁿ
norig? oe (ε ≾̂ₑᶜ ε')   = just ≾ₑⁿ
norig? oe (Etᶜ A)      = just Etⁿ
norig? oe (Et∨≾ᵘ A ρ)  = just Et∨ⁿ
norig? oe (∃ᵗ C) with norig? oe C
... | just p  = just (∃ᵗⁿ p)
... | nothing = nothing
norig? oe (∃ʳ C) with norig? oe C
... | just p  = just (∃ʳⁿ p)
... | nothing = nothing
norig? oe (∃ᵉ C) with norig? oe C
... | just p  = just (∃ᵉⁿ p)
... | nothing = nothing
norig? oe (∀ᵉ C)       = nothing
norig? oe (⋀ᵒᵖ f) with all-build (λ op → norig? oe (f op)) (OpEnum.ops oe)
... | just ps = just (⋀ⁿ (λ op → all-lookup ps (OpEnum.complete oe op)))
... | nothing = nothing
