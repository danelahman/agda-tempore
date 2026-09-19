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
--                                                                --
-- The name follows OutsideIn(X): a residual constraint is what    --
-- solving leaves behind (Vytiniotis et al., JFP 2011).            --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Sum.Base using ([_,_]′)

open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Resid (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (EternalBaseType; eternalBaseType?)

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S
open import TypeInference.Open.Hyps   S

open import TypeInference.SolverImpl.Core.Rigid S using (zip₂; zip₂-just)

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

-- Conversely, every atom of a successful decomposition is entailed
-- by the demand it came from.

etDec-compl : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (A : OVType Ψ) → {αs : List (TyVar Ψ)}
            → etDec A ≡ just αs → (δ : Subst Ψ Ψ') → Q ⊩ᴱ A [ δ ]ᵛ
            → ∀ {α} → α ∈ αs → Q ⊩ᴱ tvar α [ δ ]ᵛ
etDec-compl (tvar β) refl δ et (here refl) = et
etDec-compl (Base b) q δ et with eternalBaseType? b
etDec-compl (Base b) refl δ et | yes p = λ ()
etDec-compl (Base b) ()   δ et | no ¬p
etDec-compl Unit  refl δ et = λ ()
etDec-compl Bool  refl δ et = λ ()
etDec-compl Empty refl δ et = λ ()
etDec-compl (A |×| B) q δ (p |×|ₑ p') with zip₂-just _++_ (etDec A) (etDec B) q
... | as , bs , qa , qb , refl =
      λ m → [ etDec-compl A qa δ p , etDec-compl B qb δ p' ]′ (∈-++⁻ as m)
etDec-compl (A ⇒ C)   () δ et
etDec-compl ([ ρ ] A) () δ et

-- A failed decomposition refutes the demand, at every instance:
-- substitution preserves the head former, and `_⊩ᴱ_` has no rule
-- for a function, a box, or a non-eternal base type.

etDec-refute : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (A : OVType Ψ) → etDec A ≡ nothing
             → (δ : Subst Ψ Ψ') → ¬ (Q ⊩ᴱ A [ δ ]ᵛ)
etDec-refute (tvar α) () δ
etDec-refute (Base b) q δ with eternalBaseType? b
etDec-refute (Base b) () δ | yes p
etDec-refute (Base b) q  δ | no ¬p = λ { (Baseₑ p') → ⊥-elim-irr (¬p p') }
etDec-refute Unit      () δ
etDec-refute Bool      () δ
etDec-refute Empty     () δ
etDec-refute (A |×| B) q δ with etDec A in e₁ | etDec B in e₂
etDec-refute (A |×| B) () δ | just _  | just _
etDec-refute (A |×| B) q  δ | just _  | nothing =
  λ { (p |×|ₑ p') → etDec-refute B e₂ δ p' }
etDec-refute (A |×| B) q  δ | nothing | _       =
  λ { (p |×|ₑ p') → etDec-refute A e₁ δ p }
etDec-refute (A ⇒ C)   q δ = λ ()
etDec-refute ([ ρ ] A) q δ = λ ()

--------------------------------------------------------------
-- Reading a residual back as a hypothesis set               --
--                                                           --
-- The decomposition is paired with the entailment it         --
-- justifies, so that the case analysis of `etsList` stays    --
-- visible to a proof about it.                               --
--------------------------------------------------------------

EtDec : ∀ {Ψ} → OVType Ψ → Set
EtDec {Ψ} A = Σ[ αs ∈ List (TyVar Ψ) ]
                ({Q : Hyps Ψ} → (∀ {α} → α ∈ αs → Q ⊩ᴱ tvar α) → Q ⊩ᴱ A)

etDecAt : ∀ {Ψ} → (A : OVType Ψ) → (x : Maybe (List (TyVar Ψ))) → etDec A ≡ x
        → Maybe (EtDec A)
etDecAt A (just αs) eq = just (αs , λ k → etDec-sound A eq k)
etDecAt A nothing   eq = nothing

etDec⁺ : ∀ {Ψ} → (A : OVType Ψ) → Maybe (EtDec A)
etDec⁺ A = etDecAt A (etDec A) refl

etDecAt-nothing : ∀ {Ψ} → (A : OVType Ψ) → (x : Maybe (List (TyVar Ψ)))
                → (eq : etDec A ≡ x) → etDecAt A x eq ≡ nothing → etDec A ≡ nothing
etDecAt-nothing A nothing  eq q = eq
etDecAt-nothing A (just _) eq ()

etDec⁺-nothing : ∀ {Ψ} → (A : OVType Ψ) → etDec⁺ A ≡ nothing → etDec A ≡ nothing
etDec⁺-nothing A q = etDecAt-nothing A (etDec A) refl q

etDecAt-just : ∀ {Ψ} → (A : OVType Ψ) → (x : Maybe (List (TyVar Ψ)))
             → (eq : etDec A ≡ x) → {p : EtDec A} → etDecAt A x eq ≡ just p
             → etDec A ≡ just (proj₁ p)
etDecAt-just A (just as) eq refl = eq
etDecAt-just A nothing   eq ()

etDec⁺-just : ∀ {Ψ} → (A : OVType Ψ) → {p : EtDec A} → etDec⁺ A ≡ just p
            → etDec A ≡ just (proj₁ p)
etDec⁺-just A q = etDecAt-just A (etDec A) refl q

etsList : ∀ {Ψ} → (l : List (OVType Ψ))
        → Maybe (Σ[ αs ∈ List (TyVar Ψ) ]
                  ({Q : Hyps Ψ} → (∀ {α} → α ∈ αs → Q ⊩ᴱ tvar α)
                   → ∀ {A} → A ∈ l → Q ⊩ᴱ A))
etsList []      = just ([] , λ k ())
etsList (A ∷ l) with etDec⁺ A | etsList l
... | just (as , g) | just (bs , f) =
      just (as ++ bs ,
            λ k → λ { (here refl) → g (λ m → k (∈-++⁺ˡ m))
                    ; (there m)   → f (λ m' → k (∈-++⁺ʳ as m')) m })
... | just _        | nothing = nothing
... | nothing       | _       = nothing

-- A failure names an undecomposable demand

etsList-nothing : ∀ {Ψ} → (l : List (OVType Ψ)) → etsList l ≡ nothing
                → Σ[ A ∈ OVType Ψ ] ((A ∈ l) × (etDec A ≡ nothing))
etsList-nothing []      ()
etsList-nothing (A ∷ l) eq with etDec⁺ A in e₀ | etsList l in e
etsList-nothing (A ∷ l) () | just _ | just _
etsList-nothing (A ∷ l) eq | just _ | nothing with etsList-nothing l e
... | B , m , q = B , there m , q
etsList-nothing (A ∷ l) eq | nothing | _ = A , here refl , etDec⁺-nothing A e₀

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

-- The same, for a whole residual

toHyps-nothing : ∀ {Ψ} → (R : Resid Ψ) → toHyps R ≡ nothing
               → Σ[ A ∈ OVType Ψ ] ((A ∈ ts R) × (etDec A ≡ nothing))
toHyps-nothing R eq with etsList (ts R) in e
... | nothing = etsList-nothing (ts R) e
toHyps-nothing R () | just _

-- Every atom the read-back raised is entailed by the demands it
-- came from, at every instance

etsList-compl : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (l : List (OVType Ψ))
              → {p : Σ[ αs ∈ List (TyVar Ψ) ]
                       ({Q' : Hyps Ψ} → (∀ {α} → α ∈ αs → Q' ⊩ᴱ tvar α)
                        → ∀ {A} → A ∈ l → Q' ⊩ᴱ A)}
              → etsList l ≡ just p → (δ : Subst Ψ Ψ')
              → (∀ {A} → A ∈ l → Q ⊩ᴱ A [ δ ]ᵛ)
              → ∀ {α} → α ∈ proj₁ p → Q ⊩ᴱ tvar α [ δ ]ᵛ
etsList-compl []      refl δ k = λ ()
etsList-compl (A ∷ l) eq   δ k with etDec⁺ A in e₀ | etsList l in e
etsList-compl (A ∷ l) ()   δ k | just _ | nothing
etsList-compl (A ∷ l) ()   δ k | nothing | _
etsList-compl (A ∷ l) eq   δ k | just (as , g) | just (bs , f) with eq
... | refl = λ m → [ etDec-compl A (etDec⁺-just A e₀) δ (k (here refl))
                   , etsList-compl l e δ (λ m' → k (there m')) ]′ (∈-++⁻ as m)

toHyps-compl : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (R : Resid Ψ)
             → {p : Σ[ Q₀ ∈ Hyps Ψ ] (Q₀ ⊩ᴿ R [ idˢ ])}
             → toHyps R ≡ just p → (δ : Subst Ψ Ψ')
             → Q ⊩ᴿ R [ δ ] → Q ⊩ᴴ proj₁ p [ δ ]
toHyps-compl R eq δ h with etsList (ts R) in e
toHyps-compl R () δ h | nothing
toHyps-compl R eq δ h | just (αs , f) with eq
... | refl = mk⊩ᴴ (etsList-compl (ts R) e δ (⊩ts h)) (⊩rs h) (⊩es h)
