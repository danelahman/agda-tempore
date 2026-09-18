------------------------------------------------------------------
-- Residual constraints                                          --
--                                                                --
-- What the driver cannot solve it carries: a `Resid Ψ` is the    --
-- list of grade orderings and eternality demands still open over  --
-- the current scope. Unlike `Hyps`, a residual is closed under    --
-- substitution — its eternality component holds whole types, not  --
-- variables — which is what lets the driver push it through the   --
-- store extensions a unification performs.                        --
--                                                                --
-- `Q ⊩ᴿ R [ δ ]` is what it takes to discharge a residual: every  --
-- atom, instantiated along `δ`, is entailed by `Q`. Reading a     --
-- residual back as a hypothesis set (`toHyps`) decomposes the     --
-- eternality demands into atoms on type variables (`etDec`) and   --
-- takes the orderings verbatim.                                   --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import Inference.Scopes

module Inference.SolverImpl.Resid (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (EternalBaseType; eternalBaseType?)

open import Inference.Open.Grades S
open import Inference.Open.Types  S
open import Inference.Open.Subst  S
open import Inference.Open.Hyps   S

open import Inference.SolverImpl.Core.Rigid S using (zip₂; zip₂-just)

--------------------------------------------------------------
-- Residuals                                                 --
--------------------------------------------------------------

record Resid (Ψ : Scope) : Set where
  constructor resid
  field
    rs : List (RExp Ψ × RExp Ψ)            -- open resource-grade orderings
    es : List (EExp Ψ × EExp Ψ)            -- open effect-grade orderings
    ts : List (OVType Ψ)                   -- open eternality demands

open Resid public

emptyᴿ : ∀ {Ψ} → Resid Ψ
emptyᴿ = resid [] [] []

infixl 50 _[_]ᴿ
infixr 5 _∪ᴿ_

_[_]ᴿ : ∀ {Ψ Ψ'} → Resid Ψ → Subst Ψ Ψ' → Resid Ψ'
R [ σ ]ᴿ = resid (map (mapᵖ (_[ σ ]ʳ)) (rs R))
                 (map (mapᵖ (_[ σ ]ᵉ)) (es R))
                 (map (_[ σ ]ᵛ) (ts R))

_∪ᴿ_ : ∀ {Ψ} → Resid Ψ → Resid Ψ → Resid Ψ
R ∪ᴿ R' = resid (rs R ++ rs R') (es R ++ es R') (ts R ++ ts R')

-- Pushing one atom

pushʳ : ∀ {Ψ} → RExp Ψ → RExp Ψ → Resid Ψ → Resid Ψ
pushʳ ρ ρ' R = resid ((ρ , ρ') ∷ rs R) (es R) (ts R)

pushᵉ : ∀ {Ψ} → EExp Ψ → EExp Ψ → Resid Ψ → Resid Ψ
pushᵉ ε ε' R = resid (rs R) ((ε , ε') ∷ es R) (ts R)

pushᵗ : ∀ {Ψ} → OVType Ψ → Resid Ψ → Resid Ψ
pushᵗ A R = resid (rs R) (es R) (A ∷ ts R)

--------------------------------------------------------------
-- Discharging a residual                                    --
--------------------------------------------------------------

infix 4 _⊩ᴿ_[_]

record _⊩ᴿ_[_] {Ψ Ψ' : Scope} (Q : Hyps Ψ') (R : Resid Ψ) (δ : Subst Ψ Ψ') : Set where
  constructor mk⊩ᴿ
  field
    ⊩rs : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    ⊩es : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
    ⊩ts : ∀ {A}    → A ∈ ts R        → Q ⊩ᴱ A [ δ ]ᵛ

open _⊩ᴿ_[_] public

⊩ᴿ-empty : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → Q ⊩ᴿ emptyᴿ [ δ ]
⊩ᴿ-empty = mk⊩ᴿ (λ ()) (λ ()) (λ ())

⊩ᴿ-resp-≐ˢ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {δ δ' : Subst Ψ Ψ'}
           → δ ≐ˢ δ' → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ R [ δ' ]
⊩ᴿ-resp-≐ˢ {Q = Q} p h =
  mk⊩ᴿ (λ {ρ} {ρ'} m → subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([≐]ʳ p ρ) ([≐]ʳ p ρ') (⊩rs h m))
       (λ {ε} {ε'} m → subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([≐]ᵉ p ε) ([≐]ᵉ p ε') (⊩es h m))
       (λ {A}       m → subst (Q ⊩ᴱ_) ([≐]ᵛ p A) (⊩ts h m))

-- A residual pushed through a substitution

⊩ᴿ-subst : ∀ {Ψ Ψ₁ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ}
             {σ : Subst Ψ Ψ₁} {δ : Subst Ψ₁ Ψ'}
         → Q ⊩ᴿ (R [ σ ]ᴿ) [ δ ] → Q ⊩ᴿ R [ σ ⨟ˢ δ ]
⊩ᴿ-subst {Q = Q} {σ = σ} {δ = δ} h =
  mk⊩ᴿ (λ {ρ} {ρ'} m → subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([⨟]ʳ ρ σ δ) ([⨟]ʳ ρ' σ δ)
                              (⊩rs h (∈-map⁺ (mapᵖ (_[ σ ]ʳ)) m)))
       (λ {ε} {ε'} m → subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([⨟]ᵉ ε σ δ) ([⨟]ᵉ ε' σ δ)
                              (⊩es h (∈-map⁺ (mapᵖ (_[ σ ]ᵉ)) m)))
       (λ {A}      m → subst (Q ⊩ᴱ_) ([⨟]ᵛ A σ δ)
                              (⊩ts h (∈-map⁺ (_[ σ ]ᵛ) m)))

-- A discharge followed by a strengthening of the hypotheses

⊩ᴿ-⨟ : ∀ {Ψ Ψ' Ψ''} {Q : Hyps Ψ'} {Q' : Hyps Ψ''} {R : Resid Ψ}
         {δ : Subst Ψ Ψ'} {δ' : Subst Ψ' Ψ''}
     → Q' ⊩ᴴ Q [ δ' ] → Q ⊩ᴿ R [ δ ] → Q' ⊩ᴿ R [ δ ⨟ˢ δ' ]
⊩ᴿ-⨟ {Q' = Q'} {δ = δ} {δ' = δ'} g h =
  mk⊩ᴿ (λ {ρ} {ρ'} m → subst₂ (λ x y → Q' ⊩ x ≾̂ᵣ y) ([⨟]ʳ ρ δ δ') ([⨟]ʳ ρ' δ δ')
                              (⊩-substᵣ g (⊩rs h m)))
       (λ {ε} {ε'} m → subst₂ (λ x y → Q' ⊩ x ≾̂ₑ y) ([⨟]ᵉ ε δ δ') ([⨟]ᵉ ε' δ δ')
                              (⊩-substₑ g (⊩es h m)))
       (λ {A}      m → subst (Q' ⊩ᴱ_) ([⨟]ᵛ A δ δ') (⊩ᴱ-subst g (⊩ts h m)))

-- The two components of a union

∪ᴿ-fst : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R R' : Resid Ψ} {δ : Subst Ψ Ψ'}
       → Q ⊩ᴿ (R ∪ᴿ R') [ δ ] → Q ⊩ᴿ R [ δ ]
∪ᴿ-fst h = mk⊩ᴿ (λ m → ⊩rs h (∈-++⁺ˡ m))
                (λ m → ⊩es h (∈-++⁺ˡ m))
                (λ m → ⊩ts h (∈-++⁺ˡ m))

∪ᴿ-snd : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R R' : Resid Ψ} {δ : Subst Ψ Ψ'}
       → Q ⊩ᴿ (R ∪ᴿ R') [ δ ] → Q ⊩ᴿ R' [ δ ]
∪ᴿ-snd {R = R} h = mk⊩ᴿ (λ m → ⊩rs h (∈-++⁺ʳ (rs R) m))
                        (λ m → ⊩es h (∈-++⁺ʳ (es R) m))
                        (λ m → ⊩ts h (∈-++⁺ʳ (ts R) m))

-- The tail of a residual with one atom pushed

tailʳ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {ρ ρ' : RExp Ψ} {δ : Subst Ψ Ψ'}
      → Q ⊩ᴿ (pushʳ ρ ρ' R) [ δ ] → Q ⊩ᴿ R [ δ ]
tailʳ h = mk⊩ᴿ (λ m → ⊩rs h (there m)) (⊩es h) (⊩ts h)

tailᵉ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {ε ε' : EExp Ψ} {δ : Subst Ψ Ψ'}
      → Q ⊩ᴿ (pushᵉ ε ε' R) [ δ ] → Q ⊩ᴿ R [ δ ]
tailᵉ h = mk⊩ᴿ (⊩rs h) (λ m → ⊩es h (there m)) (⊩ts h)

tailᵗ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {A : OVType Ψ} {δ : Subst Ψ Ψ'}
      → Q ⊩ᴿ (pushᵗ A R) [ δ ] → Q ⊩ᴿ R [ δ ]
tailᵗ h = mk⊩ᴿ (⊩rs h) (⊩es h) (λ m → ⊩ts h (there m))

-- The empty hypothesis set entails nothing, so every decision taken
-- against it transports to any hypothesis set and any substitution

∅ᴴ-⊩ᴴ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → Q ⊩ᴴ ∅ᴴ [ δ ]
∅ᴴ-⊩ᴴ = mk⊩ᴴ (λ ()) (λ ()) (λ ())

--------------------------------------------------------------
-- Eternality, decomposed                                    --
--                                                           --
-- `_⊩ᴱ_` has one rule per former except `_⇒_` and `[_]_`,   --
-- and `et-hyp` at a type variable, so a demand either        --
-- reduces to demands on type variables or is refuted.        --
--------------------------------------------------------------

etDec : ∀ {Ψ} → OVType Ψ → Maybe (List (TyVar Ψ))
etDec (tvar α)  = just (α ∷ [])
etDec (Base b)  with eternalBaseType? b
... | yes _ = just []
... | no _  = nothing
etDec Unit      = just []
etDec Bool      = just []
etDec (A |×| B) = zip₂ _++_ (etDec A) (etDec B)
etDec Empty     = just []
etDec (A ⇒ C)   = nothing
etDec ([ ρ ] A) = nothing

etDec-sound : ∀ {Ψ} {Q : Hyps Ψ} → (A : OVType Ψ) → {αs : List (TyVar Ψ)}
            → etDec A ≡ just αs → (∀ {α} → α ∈ αs → Q ⊩ᴱ tvar α) → Q ⊩ᴱ A
etDec-sound (tvar α) refl k = k (here refl)
etDec-sound (Base b) q k with eternalBaseType? b
etDec-sound (Base b) refl k | yes p = Baseₑ p
etDec-sound Unit  refl k = Unitₑ
etDec-sound Bool  refl k = Boolₑ
etDec-sound Empty refl k = Emptyₑ
etDec-sound (A |×| B) q k with zip₂-just _++_ (etDec A) (etDec B) q
... | as , bs , qa , qb , refl =
      etDec-sound A qa (λ m → k (∈-++⁺ˡ m)) |×|ₑ
      etDec-sound B qb (λ m → k (∈-++⁺ʳ as m))

--------------------------------------------------------------
-- Reading a residual back as a hypothesis set               --
--------------------------------------------------------------

etsList : ∀ {Ψ} → (l : List (OVType Ψ))
        → Maybe (Σ[ αs ∈ List (TyVar Ψ) ]
                  ({Q : Hyps Ψ} → (∀ {α} → α ∈ αs → Q ⊩ᴱ tvar α)
                   → ∀ {A} → A ∈ l → Q ⊩ᴱ A))
etsList []      = just ([] , λ k ())
etsList (A ∷ l) with etDec A in eq | etsList l
... | just as | just (bs , f) =
      just (as ++ bs ,
            λ k → λ { (here refl) → etDec-sound A eq (λ m → k (∈-++⁺ˡ m))
                    ; (there m)   → f (λ m' → k (∈-++⁺ʳ as m')) m })
... | just _  | nothing = nothing
... | nothing | _       = nothing

toHyps : ∀ {Ψ} → (R : Resid Ψ) → Maybe (Σ[ Q ∈ Hyps Ψ ] (Q ⊩ᴿ R [ idˢ ]))
toHyps R with etsList (ts R)
... | nothing       = nothing
... | just (αs , f) = just (Q , mk⊩ᴿ ordᵣ' ordₑ' ets')
  where
    Q : Hyps _
    Q = hyps αs (rs R) (es R)

    ets' : ∀ {A} → A ∈ ts R → Q ⊩ᴱ A [ idˢ ]ᵛ
    ets' {A} m = subst (Q ⊩ᴱ_) (sym ([id]ᵛ A)) (f et-hyp m)

    ordᵣ' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ idˢ ]ʳ ≾̂ᵣ ρ' [ idˢ ]ʳ
    ordᵣ' {ρ} {ρ'} m =
      subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([id]ʳ ρ)) (sym ([id]ʳ ρ')) (hypᵣ m)

    ordₑ' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ idˢ ]ᵉ ≾̂ₑ ε' [ idˢ ]ᵉ
    ordₑ' {ε} {ε'} m =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([id]ᵉ ε)) (sym ([id]ᵉ ε')) (hypₑ m)
