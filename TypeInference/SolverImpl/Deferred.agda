------------------------------------------------------------------
-- Deferred rigid conditions                                      --
--                                                                --
-- A clause's grade orderings that mix its rigid with outer       --
-- unknowns are deferred as an entry `∀ᵉ j₁ … jₖ. O`: orderings    --
-- over the scope extended by `k` rigids, `j₁` outermost,          --
-- labelled with the operation of the clause that left them. An   --
-- entry is discharged along a substitution when its orderings    --
-- are, at fresh rigids, by the hypotheses weakened to them: it   --
-- reads back as an obligation (`toOblig`).                       --
--                                                                --
-- A substitution below (above) the one it moves keeps an entry   --
-- whose greater (smaller) sides it leaves fixed (`keepᵈ`). A     --
-- closed witness per rigid instantiates the rigids (`wit`).      --
--                                                                --
-- Contract. An entry and its obligation hold together            --
-- (`⊩ᵈ→⊩ᴼ`, `⊩ᴼ→⊩ᵈ`). Closing an entry over one more rigid       --
-- (`closeᵈ`) holds exactly where the entry does at a fresh rigid --
-- (`closeᵈ-sound`, `closeᵈ-princ`). Retrying the entries is the  --
-- driver's (`retry`, `SolverImpl.Solve`).                        --
------------------------------------------------------------------

open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.List.Properties using (≡-dec)

open import Relation.Nullary using (Dec; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Deferred (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops using (Op)

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S
  using (_+eⁿ_; _↑ᵉⁿ_; wkᵉⁿ-H; ≐ˢ-↑ᵉⁿ; Oblig; oblig; Obligs; _⊩ᴼ_[_]; _⊩ᴼˢ_[_])
open import TypeInference.Constraints.Properties S using (⊩ᴴ-↑ᵉ)

------------------------------------------------------------------------
-- Lifting over the rigids

⨟-↑ᵉⁿ : ∀ {Θ Θ₁ Θ₂} → (σ : Subst Θ Θ₁) → (δ : Subst Θ₁ Θ₂) → (k : ℕ)
      → ((σ ↑ᵉⁿ k) ⨟ˢ (δ ↑ᵉⁿ k)) ≐ˢ ((σ ⨟ˢ δ) ↑ᵉⁿ k)
⨟-↑ᵉⁿ σ δ zero    = ≐ˢ-refl
⨟-↑ᵉⁿ σ δ (suc k) = ≐ˢ-trans (⨟-↑ᵉⁿ (σ ↑ᵉ) (δ ↑ᵉ) k) (≐ˢ-↑ᵉⁿ (⨟-↑ᵉ σ δ) k)

⊩ᴴ-↑ᵉⁿ : ∀ {Θ Θ'} {Q : Hyps Θ} {Q' : Hyps Θ'} {δ : Subst Θ Θ'} → (k : ℕ)
       → Q' ⊩ᴴ Q [ δ ] → wkᵉⁿ-H k Q' ⊩ᴴ wkᵉⁿ-H k Q [ δ ↑ᵉⁿ k ]
⊩ᴴ-↑ᵉⁿ zero    h = h
⊩ᴴ-↑ᵉⁿ (suc k) h = ⊩ᴴ-↑ᵉⁿ k (⊩ᴴ-↑ᵉ h)

≾ˢ-↑ᵉ : ∀ {Θ Θ'} {Q : Hyps Θ'} {σ τ : Subst Θ Θ'}
      → Q ⊩ σ ≾ˢ τ → wkᵉ-H Q ⊩ (σ ↑ᵉ) ≾ˢ (τ ↑ᵉ)
≾ˢ-↑ᵉ p = mk≾ˢ (λ i → ⊩-wkᵉᵣ (≾ˢʳ p i))
               (λ { zero → ⊩≾̂ₑ-refl ; (suc i) → ⊩-wkᵉₑ (≾ˢᵉ p i) })

≾ˢ-↑ᵉⁿ : ∀ {Θ Θ'} {Q : Hyps Θ'} {σ τ : Subst Θ Θ'} → (k : ℕ)
       → Q ⊩ σ ≾ˢ τ → wkᵉⁿ-H k Q ⊩ (σ ↑ᵉⁿ k) ≾ˢ (τ ↑ᵉⁿ k)
≾ˢ-↑ᵉⁿ zero    p = p
≾ˢ-↑ᵉⁿ (suc k) p = ≾ˢ-↑ᵉⁿ k (≾ˢ-↑ᵉ p)

wkᵉⁿ-∅ : ∀ {Θ} → (k : ℕ) → wkᵉⁿ-H k (∅ᴴ {Θ}) ≡ ∅ᴴ
wkᵉⁿ-∅ zero    = refl
wkᵉⁿ-∅ (suc k) = wkᵉⁿ-∅ k

------------------------------------------------------------------------
-- Grade orderings

record Ords (Ψ : Scope) : Set where
  constructor ords
  field
    ors : List (RExp Ψ × RExp Ψ)
    oes : List (EExp Ψ × EExp Ψ)

open Ords public

infixl 50 _[_]ᴼ

_[_]ᴼ : ∀ {Ψ Ψ'} → Ords Ψ → Subst Ψ Ψ' → Ords Ψ'
o [ σ ]ᴼ = ords (map (mapᵖ (_[ σ ]ʳ)) (ors o)) (map (mapᵖ (_[ σ ]ᵉ)) (oes o))

infix 4 _⊩ᵒ_[_]

record _⊩ᵒ_[_] {Ψ Ψ' : Scope} (Q : Hyps Ψ') (o : Ords Ψ) (δ : Subst Ψ Ψ') : Set where
  constructor mk⊩ᵒ
  field
    ⊩ors : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors o → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    ⊩oes : ∀ {ε ε'} → (ε , ε') ∈ oes o → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ

open _⊩ᵒ_[_] public

⊩ᵒ-resp-≐ˢ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {o : Ords Ψ} {δ δ' : Subst Ψ Ψ'}
           → δ ≐ˢ δ' → Q ⊩ᵒ o [ δ ] → Q ⊩ᵒ o [ δ' ]
⊩ᵒ-resp-≐ˢ {Q = Q} p h =
  mk⊩ᵒ (λ {ρ} {ρ'} m → subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([≐]ʳ p ρ) ([≐]ʳ p ρ') (⊩ors h m))
       (λ {ε} {ε'} m → subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([≐]ᵉ p ε) ([≐]ᵉ p ε') (⊩oes h m))

⊩ᵒ-subst : ∀ {Ψ Ψ₁ Ψ'} {Q : Hyps Ψ'} {o : Ords Ψ} {σ : Subst Ψ Ψ₁} {δ : Subst Ψ₁ Ψ'}
         → Q ⊩ᵒ o [ σ ]ᴼ [ δ ] → Q ⊩ᵒ o [ σ ⨟ˢ δ ]
⊩ᵒ-subst {Q = Q} {σ = σ} {δ} h =
  mk⊩ᵒ (λ {ρ} {ρ'} m → subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([⨟]ʳ ρ σ δ) ([⨟]ʳ ρ' σ δ)
                              (⊩ors h (∈-map⁺ (mapᵖ (_[ σ ]ʳ)) m)))
       (λ {ε} {ε'} m → subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([⨟]ᵉ ε σ δ) ([⨟]ᵉ ε' σ δ)
                              (⊩oes h (∈-map⁺ (mapᵖ (_[ σ ]ᵉ)) m)))

⊩ᵒ-subst⁻ : ∀ {Ψ Ψ₁ Ψ'} {Q : Hyps Ψ'} {o : Ords Ψ} {σ : Subst Ψ Ψ₁} {δ : Subst Ψ₁ Ψ'}
          → Q ⊩ᵒ o [ σ ⨟ˢ δ ] → Q ⊩ᵒ o [ σ ]ᴼ [ δ ]
⊩ᵒ-subst⁻ {Q = Q} {o = o} {σ = σ} {δ} h = mk⊩ᵒ r e
  where
    r : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors (o [ σ ]ᴼ) → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    r m with ∈-map⁻ (mapᵖ (_[ σ ]ʳ)) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([⨟]ʳ ρ₀ σ δ)) (sym ([⨟]ʳ ρ₀' σ δ)) (⊩ors h m₀)

    e : ∀ {ε ε'} → (ε , ε') ∈ oes (o [ σ ]ᴼ) → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
    e m with ∈-map⁻ (mapᵖ (_[ σ ]ᵉ)) m
    ... | (ε₀ , ε₀') , m₀ , refl =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([⨟]ᵉ ε₀ σ δ)) (sym ([⨟]ᵉ ε₀' σ δ)) (⊩oes h m₀)

⊩ᵒ-⨟ : ∀ {Ψ Ψ' Ψ''} {Q : Hyps Ψ'} {Q' : Hyps Ψ''} {o : Ords Ψ}
         {δ : Subst Ψ Ψ'} {δ' : Subst Ψ' Ψ''}
     → Q' ⊩ᴴ Q [ δ' ] → Q ⊩ᵒ o [ δ ] → Q' ⊩ᵒ o [ δ ⨟ˢ δ' ]
⊩ᵒ-⨟ {Q' = Q'} {δ = δ} {δ'} g h =
  mk⊩ᵒ (λ {ρ} {ρ'} m → subst₂ (λ x y → Q' ⊩ x ≾̂ᵣ y) ([⨟]ʳ ρ δ δ') ([⨟]ʳ ρ' δ δ')
                              (⊩-substᵣ g (⊩ors h m)))
       (λ {ε} {ε'} m → subst₂ (λ x y → Q' ⊩ x ≾̂ₑ y) ([⨟]ᵉ ε δ δ') ([⨟]ᵉ ε' δ δ')
                              (⊩-substₑ g (⊩oes h m)))

------------------------------------------------------------------------
-- Entries

record Dfr (Ψ : Scope) : Set where
  constructor dfr
  field
    lbl  : Maybe Op
    nb   : ℕ
    body : Ords (Ψ +eⁿ nb)

open Dfr public

infixl 50 _[_]ᵈ

_[_]ᵈ : ∀ {Ψ Ψ'} → Dfr Ψ → Subst Ψ Ψ' → Dfr Ψ'
dfr l k o [ σ ]ᵈ = dfr l k (o [ σ ↑ᵉⁿ k ]ᴼ)

infix 4 _⊩ᵈ_[_]

_⊩ᵈ_[_] : ∀ {Ψ Ψ'} → Hyps Ψ' → Dfr Ψ → Subst Ψ Ψ' → Set
Q ⊩ᵈ E [ δ ] = wkᵉⁿ-H (nb E) Q ⊩ᵒ body E [ δ ↑ᵉⁿ nb E ]

⊩ᵈ-resp-≐ˢ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ δ' : Subst Ψ Ψ'} → (E : Dfr Ψ)
           → δ ≐ˢ δ' → Q ⊩ᵈ E [ δ ] → Q ⊩ᵈ E [ δ' ]
⊩ᵈ-resp-≐ˢ (dfr l k o) p h = ⊩ᵒ-resp-≐ˢ (≐ˢ-↑ᵉⁿ p k) h

⊩ᵈ-subst : ∀ {Ψ Ψ₁ Ψ'} {Q : Hyps Ψ'} {σ : Subst Ψ Ψ₁} {δ : Subst Ψ₁ Ψ'} → (E : Dfr Ψ)
         → Q ⊩ᵈ E [ σ ]ᵈ [ δ ] → Q ⊩ᵈ E [ σ ⨟ˢ δ ]
⊩ᵈ-subst {σ = σ} {δ} (dfr l k o) h = ⊩ᵒ-resp-≐ˢ (⨟-↑ᵉⁿ σ δ k) (⊩ᵒ-subst h)

⊩ᵈ-subst⁻ : ∀ {Ψ Ψ₁ Ψ'} {Q : Hyps Ψ'} {σ : Subst Ψ Ψ₁} {δ : Subst Ψ₁ Ψ'} → (E : Dfr Ψ)
          → Q ⊩ᵈ E [ σ ⨟ˢ δ ] → Q ⊩ᵈ E [ σ ]ᵈ [ δ ]
⊩ᵈ-subst⁻ {σ = σ} {δ} (dfr l k o) h =
  ⊩ᵒ-subst⁻ (⊩ᵒ-resp-≐ˢ (≐ˢ-sym (⨟-↑ᵉⁿ σ δ k)) h)

⊩ᵈ-⨟ : ∀ {Ψ Ψ' Ψ''} {Q : Hyps Ψ'} {Q' : Hyps Ψ''} {δ : Subst Ψ Ψ'} {δ' : Subst Ψ' Ψ''}
     → (E : Dfr Ψ) → Q' ⊩ᴴ Q [ δ' ] → Q ⊩ᵈ E [ δ ] → Q' ⊩ᵈ E [ δ ⨟ˢ δ' ]
⊩ᵈ-⨟ {δ = δ} {δ'} (dfr l k o) g h =
  ⊩ᵒ-resp-≐ˢ (⨟-↑ᵉⁿ δ δ' k) (⊩ᵒ-⨟ (⊩ᴴ-↑ᵉⁿ k g) h)

-- An entry over the scope extended by one rigid binds it outermost

bindᵈ : ∀ {Ψ} → Dfr (Ψ +e) → Dfr Ψ
bindᵈ (dfr l k o) = dfr l (suc k) o

-- An entry reads back as an obligation

ordsH : ∀ {Ψ} → Ords Ψ → Hyps Ψ
ordsH o = hyps [] [] (ors o) (oes o) []

toOblig : ∀ {Ψ} → Dfr Ψ → Oblig Ψ
toOblig (dfr l k o) = oblig l k (ordsH o)

⊩ᵈ→⊩ᴼ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (E : Dfr Ψ)
      → Q ⊩ᵈ E [ δ ] → Q ⊩ᴼ toOblig E [ δ ]
⊩ᵈ→⊩ᴼ (dfr l k o) h = mk⊩ᴴ (λ ()) (λ ()) (⊩ors h) (⊩oes h) (λ ())

⊩ᴼ→⊩ᵈ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (E : Dfr Ψ)
      → Q ⊩ᴼ toOblig E [ δ ] → Q ⊩ᵈ E [ δ ]
⊩ᴼ→⊩ᵈ (dfr l k o) h = mk⊩ᵒ (⊩ordᵣ h) (⊩ordₑ h)

⊩ᴰ→⊩ᴼˢ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (D : List (Dfr Ψ))
       → (∀ {E} → E ∈ D → Q ⊩ᵈ E [ δ ]) → Q ⊩ᴼˢ map toOblig D [ δ ]
⊩ᴰ→⊩ᴼˢ []      h = []
⊩ᴰ→⊩ᴼˢ (E ∷ D) h = ⊩ᵈ→⊩ᴼ E (h (here refl)) ∷ ⊩ᴰ→⊩ᴼˢ D (λ m → h (there m))

⊩ᴼˢ→⊩ᴰ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (D : List (Dfr Ψ))
       → Q ⊩ᴼˢ map toOblig D [ δ ] → ∀ {E} → E ∈ D → Q ⊩ᵈ E [ δ ]
⊩ᴼˢ→⊩ᴰ (E ∷ D) (h ∷ hs) (here refl) = ⊩ᴼ→⊩ᵈ E h
⊩ᴼˢ→⊩ᴰ (E ∷ D) (h ∷ hs) (there m)   = ⊩ᴼˢ→⊩ᴰ D hs m

------------------------------------------------------------------------
-- Keeping an entry under a move

data Dir : Set where
  dir↓ dir↑ : Dir

-- The move is below (`dir↓`) or above (`dir↑`) the substitution it moves

Moves : ∀ {Ψ Ψ'} → Dir → Hyps Ψ' → Subst Ψ Ψ → Subst Ψ Ψ' → Set
Moves dir↓ Q σ τ = Q ⊩ (σ ⨟ˢ τ) ≾ˢ τ
Moves dir↑ Q σ τ = Q ⊩ τ ≾ˢ (σ ⨟ˢ τ)

-- The side an ordering keeps fixed: the greater side under a move
-- down, the smaller under a move up

Fixedʳ : ∀ {Ψ} → Dir → Subst Ψ Ψ → RExp Ψ × RExp Ψ → Set
Fixedʳ dir↓ σ (x , y) = y [ σ ]ʳ ≡ y
Fixedʳ dir↑ σ (x , y) = x [ σ ]ʳ ≡ x

Fixedᵉ : ∀ {Ψ} → Dir → Subst Ψ Ψ → EExp Ψ × EExp Ψ → Set
Fixedᵉ dir↓ σ (x , y) = y [ σ ]ᵉ ≡ y
Fixedᵉ dir↑ σ (x , y) = x [ σ ]ᵉ ≡ x

fixedʳ? : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (a : RExp Ψ × RExp Ψ) → Maybe (Fixedʳ d σ a)
fixedʳ? dir↓ σ (x , y) with y [ σ ]ʳ ≟ʳ y
... | yes q = just q
... | no _  = nothing
fixedʳ? dir↑ σ (x , y) with x [ σ ]ʳ ≟ʳ x
... | yes q = just q
... | no _  = nothing

fixedᵉ? : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (a : EExp Ψ × EExp Ψ) → Maybe (Fixedᵉ d σ a)
fixedᵉ? dir↓ σ (x , y) with y [ σ ]ᵉ ≟ᵉ y
... | yes q = just q
... | no _  = nothing
fixedᵉ? dir↑ σ (x , y) with x [ σ ]ᵉ ≟ᵉ x
... | yes q = just q
... | no _  = nothing

allOf : ∀ {X : Set} {P : X → Set} → ((a : X) → Maybe (P a)) → (l : List X)
      → Maybe (∀ {a} → a ∈ l → P a)
allOf f []      = just (λ ())
allOf f (a ∷ l) with f a | allOf f l
... | just p | just g = just (λ { (here refl) → p ; (there m) → g m })
... | _      | _      = nothing

record Still {Ψ} (d : Dir) (σ : Subst Ψ Ψ) (E : Dfr Ψ) : Set where
  constructor still
  field
    stʳ : ∀ {a} → a ∈ ors (body E) → Fixedʳ d (σ ↑ᵉⁿ nb E) a
    stᵉ : ∀ {a} → a ∈ oes (body E) → Fixedᵉ d (σ ↑ᵉⁿ nb E) a

still? : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (E : Dfr Ψ) → Maybe (Still d σ E)
still? d σ E with allOf (fixedʳ? d (σ ↑ᵉⁿ nb E)) (ors (body E))
                | allOf (fixedᵉ? d (σ ↑ᵉⁿ nb E)) (oes (body E))
... | just r | just e = just (still r e)
... | _      | _      = nothing

stills? : ∀ {Ψ} → (d : Dir) → (σ : Subst Ψ Ψ) → (D : List (Dfr Ψ))
        → Maybe (∀ {E} → E ∈ D → Still d σ E)
stills? d σ = allOf (still? d σ)

keepᵈ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {σ : Subst Ψ Ψ} {τ : Subst Ψ Ψ'} → (d : Dir) → (E : Dfr Ψ)
      → Still d σ E → Moves d Q σ τ → Q ⊩ᵈ E [ τ ] → Q ⊩ᵈ E [ σ ⨟ˢ τ ]
keepᵈ {Q = Q} {σ} {τ} d (dfr l k o) (still sr se) mv h = mk⊩ᵒ (r d sr mv) (e d se mv)
  where
    Q' = wkᵉⁿ-H k Q

    fixr : (y : RExp _) → y [ σ ↑ᵉⁿ k ]ʳ ≡ y → y [ τ ↑ᵉⁿ k ]ʳ ≡ y [ (σ ⨟ˢ τ) ↑ᵉⁿ k ]ʳ
    fixr y q = trans (cong (_[ τ ↑ᵉⁿ k ]ʳ) (sym q))
                     (trans ([⨟]ʳ y (σ ↑ᵉⁿ k) (τ ↑ᵉⁿ k)) ([≐]ʳ (⨟-↑ᵉⁿ σ τ k) y))

    fixe : (y : EExp _) → y [ σ ↑ᵉⁿ k ]ᵉ ≡ y → y [ τ ↑ᵉⁿ k ]ᵉ ≡ y [ (σ ⨟ˢ τ) ↑ᵉⁿ k ]ᵉ
    fixe y q = trans (cong (_[ τ ↑ᵉⁿ k ]ᵉ) (sym q))
                     (trans ([⨟]ᵉ y (σ ↑ᵉⁿ k) (τ ↑ᵉⁿ k)) ([≐]ᵉ (⨟-↑ᵉⁿ σ τ k) y))

    r : (d : Dir) → (∀ {a} → a ∈ ors o → Fixedʳ d (σ ↑ᵉⁿ k) a) → Moves d Q σ τ
      → ∀ {x y} → (x , y) ∈ ors o → Q' ⊩ x [ (σ ⨟ˢ τ) ↑ᵉⁿ k ]ʳ ≾̂ᵣ y [ (σ ⨟ˢ τ) ↑ᵉⁿ k ]ʳ
    r dir↓ sr mv {x} {y} m =
      transᵣ (mono-substᵣ (≾ˢ-↑ᵉⁿ k mv) x)
             (subst (λ z → Q' ⊩ x [ τ ↑ᵉⁿ k ]ʳ ≾̂ᵣ z) (fixr y (sr m)) (⊩ors h m))
    r dir↑ sr mv {x} {y} m =
      transᵣ (subst (λ z → Q' ⊩ z ≾̂ᵣ y [ τ ↑ᵉⁿ k ]ʳ) (fixr x (sr m)) (⊩ors h m))
             (mono-substᵣ (≾ˢ-↑ᵉⁿ k mv) y)

    e : (d : Dir) → (∀ {a} → a ∈ oes o → Fixedᵉ d (σ ↑ᵉⁿ k) a) → Moves d Q σ τ
      → ∀ {x y} → (x , y) ∈ oes o → Q' ⊩ x [ (σ ⨟ˢ τ) ↑ᵉⁿ k ]ᵉ ≾̂ₑ y [ (σ ⨟ˢ τ) ↑ᵉⁿ k ]ᵉ
    e dir↓ se mv {x} {y} m =
      transₑ (mono-substₑ (≾ˢ-↑ᵉⁿ k mv) x)
             (subst (λ z → Q' ⊩ x [ τ ↑ᵉⁿ k ]ᵉ ≾̂ₑ z) (fixe y (se m)) (⊩oes h m))
    e dir↑ se mv {x} {y} m =
      transₑ (subst (λ z → Q' ⊩ z ≾̂ₑ y [ τ ↑ᵉⁿ k ]ᵉ) (fixe x (se m)) (⊩oes h m))
             (mono-substₑ (≾ˢ-↑ᵉⁿ k mv) y)

------------------------------------------------------------------------
-- The rigids at closed witnesses

-- `κ⟨ b ⟩` sends the newest effect-grade variable to `b`, fixing the
-- rest

κ⟨_⟩ : ∀ {Ψ} → EExp Ψ → Subst (Ψ +e) Ψ
κ⟨ b ⟩ = sub tvar rvar (λ { zero → b ; (suc i) → evar i })

wk-κ : ∀ {Ψ} → (b : EExp Ψ) → (wkˢᵉ {Ψ} ⨟ˢ κ⟨ b ⟩) ≐ˢ idˢ
wk-κ b = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

κ-wkᵛ : ∀ {Ψ} → (b : EExp Ψ) → (A : OVType Ψ) → A [ wkˢᵉ ]ᵛ [ κ⟨ b ⟩ ]ᵛ ≡ A
κ-wkᵛ b A = trans ([⨟]ᵛ A wkˢᵉ κ⟨ b ⟩) (trans ([≐]ᵛ (wk-κ b) A) ([id]ᵛ A))

κ-wkʳ : ∀ {Ψ} → (b : EExp Ψ) → (ρ : RExp Ψ) → ρ [ wkˢᵉ ]ʳ [ κ⟨ b ⟩ ]ʳ ≡ ρ
κ-wkʳ b ρ = trans ([⨟]ʳ ρ wkˢᵉ κ⟨ b ⟩) (trans ([≐]ʳ (wk-κ b) ρ) ([id]ʳ ρ))

κ-wkᵉ : ∀ {Ψ} → (b : EExp Ψ) → (ε : EExp Ψ) → ε [ wkˢᵉ ]ᵉ [ κ⟨ b ⟩ ]ᵉ ≡ ε
κ-wkᵉ b ε = trans ([⨟]ᵉ ε wkˢᵉ κ⟨ b ⟩) (trans ([≐]ᵉ (wk-κ b) ε) ([id]ᵉ ε))

-- Every weakened hypothesis is entailed back by the original set

⊩ᴴ-κ : ∀ {Ψ} {Q : Hyps Ψ} → (b : EExp Ψ) → Q ⊩ᴴ (wkᵉ-H Q) [ κ⟨ b ⟩ ]
⊩ᴴ-κ {Ψ} {Q} b = mk⊩ᴴ ets' subᵥ' ordᵣ' ordₑ' disj'
  where
    ets' : ∀ {α} → α ∈ ets (wkᵉ-H Q) → Q ⊩ᴱ sTy κ⟨ b ⟩ α
    ets' m with ∈-map⁻ (wkᵉ-tv Ψ) m
    ... | α₀ , m₀ , refl = et-hyp m₀

    subᵥ' : ∀ {α β} → (α , β) ∈ subᵥ (wkᵉ-H Q) → Q ∣ sTy κ⟨ b ⟩ α <:̂ᵛ sTy κ⟨ b ⟩ β
    subᵥ' m with ∈-map⁻ (mapᵖ (wkᵉ-tv Ψ)) m
    ... | (α₀ , β₀) , m₀ , refl = tvarₛ (hypᵗᵛ m₀)

    wkʳ' : (ρ : RExp Ψ) → ρ ≡ wkᵉ-r ρ [ κ⟨ b ⟩ ]ʳ
    wkʳ' ρ = sym (trans (cong (_[ κ⟨ b ⟩ ]ʳ) (sym (wkˢᵉ-r ρ))) (κ-wkʳ b ρ))

    wkᵉ' : (ε : EExp Ψ) → ε ≡ wkᵉ-e ε [ κ⟨ b ⟩ ]ᵉ
    wkᵉ' ε = sym (trans (cong (_[ κ⟨ b ⟩ ]ᵉ) (sym (wkˢᵉ-e ε))) (κ-wkᵉ b ε))

    wkᵛ' : (A : OVType Ψ) → A ≡ wkᵉ-v A [ κ⟨ b ⟩ ]ᵛ
    wkᵛ' A = sym (trans (cong (_[ κ⟨ b ⟩ ]ᵛ) (sym (wkˢᵉ-v A))) (κ-wkᵛ b A))

    ordᵣ' : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ (wkᵉ-H Q)
          → Q ⊩ ρ [ κ⟨ b ⟩ ]ʳ ≾̂ᵣ ρ' [ κ⟨ b ⟩ ]ʳ
    ordᵣ' m with ∈-map⁻ (mapᵖ wkᵉ-r) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (wkʳ' ρ₀) (wkʳ' ρ₀') (hypᵣ m₀)

    ordₑ' : ∀ {ε ε'} → (ε , ε') ∈ ordₑ (wkᵉ-H Q)
          → Q ⊩ ε [ κ⟨ b ⟩ ]ᵉ ≾̂ₑ ε' [ κ⟨ b ⟩ ]ᵉ
    ordₑ' m with ∈-map⁻ (mapᵖ wkᵉ-e) m
    ... | (ε₀ , ε₀') , m₀ , refl =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (wkᵉ' ε₀) (wkᵉ' ε₀') (hypₑ m₀)

    disj' : ∀ {A ρ} → (A , ρ) ∈ disj (wkᵉ-H Q) → VarOK Q (A [ κ⟨ b ⟩ ]ᵛ) (ρ [ κ⟨ b ⟩ ]ʳ)
    disj' m with ∈-map⁻ (mapᵈ wkᵉ-v wkᵉ-r) m
    ... | (A₀ , ρ₀) , m₀ , refl =
      subst₂ (VarOK Q) (wkᵛ' A₀) (wkʳ' ρ₀) (hyp-ok₀ m₀)

-- A constant commutes with a lift

↑-κ : ∀ {Ψ Ψ'} → (δ : Subst Ψ Ψ') → (c : E)
    → ((δ ↑ᵉ) ⨟ˢ κ⟨ econst c ⟩) ≐ˢ (κ⟨ econst c ⟩ ⨟ˢ δ)
↑-κ δ c =
  mk≐ˢ (λ α → trans (cong (_[ κ⟨ econst c ⟩ ]ᵛ) (sym (wkˢᵉ-v (sTy δ α))))
                    (κ-wkᵛ (econst c) (sTy δ α)))
       (λ i → trans (cong (_[ κ⟨ econst c ⟩ ]ʳ) (sym (wkˢᵉ-r (sR δ i))))
                    (κ-wkʳ (econst c) (sR δ i)))
       (λ { zero    → refl
          ; (suc i) → trans (cong (_[ κ⟨ econst c ⟩ ]ᵉ) (sym (wkˢᵉ-e (sE δ i))))
                            (κ-wkᵉ (econst c) (sE δ i)) })

-- One witness per rigid, outermost first, the unit where none is given

hdᵂ : List E → E
hdᵂ []      = uₑ
hdᵂ (c ∷ _) = c

tlᵂ : List E → List E
tlᵂ []       = []
tlᵂ (_ ∷ cs) = cs

wit : ∀ {Ψ} → (k : ℕ) → List E → Subst (Ψ +eⁿ k) Ψ
wit zero    cs = idˢ
wit (suc k) cs = wit k (tlᵂ cs) ⨟ˢ κ⟨ econst (hdᵂ cs) ⟩

-- The unit or the top for each rigid

witnesses : ℕ → List (List E)
witnesses zero    = [] ∷ []
witnesses (suc k) = map (uₑ ∷_) (witnesses k) ++ map (⊤ₑ ∷_) (witnesses k)

wit-⨟ : ∀ {Ψ Ψ'} → (δ : Subst Ψ Ψ') → (k : ℕ) → (cs : List E)
      → ((δ ↑ᵉⁿ k) ⨟ˢ wit k cs) ≐ˢ (wit k cs ⨟ˢ δ)
wit-⨟ δ zero    cs = ≐ˢ-trans (⨟-idʳ δ) (≐ˢ-sym (⨟-idˡ δ))
wit-⨟ δ (suc k) cs =
  ≐ˢ-trans (≐ˢ-sym (⨟-assoc ((δ ↑ᵉ) ↑ᵉⁿ k) (wit k (tlᵂ cs)) κ))
  (≐ˢ-trans (⨟-congˡ (wit-⨟ (δ ↑ᵉ) k (tlᵂ cs)) κ)
  (≐ˢ-trans (⨟-assoc (wit k (tlᵂ cs)) (δ ↑ᵉ) κ)
  (≐ˢ-trans (⨟-congʳ (wit k (tlᵂ cs)) (↑-κ δ (hdᵂ cs)))
            (≐ˢ-sym (⨟-assoc (wit k (tlᵂ cs)) κ δ)))))
  where
    κ : ∀ {Φ} → Subst (Φ +e) Φ
    κ = κ⟨ econst (hdᵂ cs) ⟩

-- No hypotheses entail no hypotheses at the witnesses

⊩ᴴ-wit : ∀ {Ψ} → (k : ℕ) → (cs : List E) → ∅ᴴ ⊩ᴴ wkᵉⁿ-H k (∅ᴴ {Ψ}) [ wit k cs ]
⊩ᴴ-wit {Ψ} k cs = subst (λ H → ∅ᴴ ⊩ᴴ H [ wit k cs ]) (sym (wkᵉⁿ-∅ {Ψ} k)) ⊩ᴴ-∅

------------------------------------------------------------------------
-- Closing an entry over one more rigid, the newest variable of its
-- scope: bound outermost where the entry mentions it, and dropped
-- otherwise

pair≟ : ∀ {X : Set} → ((x y : X) → Dec (x ≡ y)) → (a b : X × X) → Dec (a ≡ b)
pair≟ _≟_ (x , y) (x' , y') with x ≟ x' | y ≟ y'
... | yes refl | yes refl = yes refl
... | no ne    | _        = no (λ { refl → ne refl })
... | yes _    | no ne    = no (λ { refl → ne refl })

_≟ᴼ_ : ∀ {Ψ} → (o o' : Ords Ψ) → Dec (o ≡ o')
ords r e ≟ᴼ ords r' e' with ≡-dec (pair≟ _≟ʳ_) r r' | ≡-dec (pair≟ _≟ᵉ_) e e'
... | yes refl | yes refl = yes refl
... | no ne    | _        = no (λ { refl → ne refl })
... | yes _    | no ne    = no (λ { refl → ne refl })

closeᵈ : ∀ {Ψ} → Dfr (Ψ +e) → Dfr Ψ
closeᵈ (dfr l k o) with o [ κ⟨ ûₑ ⟩ ↑ᵉⁿ k ]ᴼ [ wkˢᵉ ↑ᵉⁿ k ]ᴼ ≟ᴼ o
... | yes _ = dfr l k (o [ κ⟨ ûₑ ⟩ ↑ᵉⁿ k ]ᴼ)
... | no _  = bindᵈ (dfr l k o)

closeᵈ-sound : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (E : Dfr (Ψ +e))
             → Q ⊩ᵈ closeᵈ E [ δ ] → wkᵉ-H Q ⊩ᵈ E [ δ ↑ᵉ ]
closeᵈ-sound {Q = Q} {δ} (dfr l k o) h with o [ κ⟨ ûₑ ⟩ ↑ᵉⁿ k ]ᴼ [ wkˢᵉ ↑ᵉⁿ k ]ᴼ ≟ᴼ o
... | no _  = h
... | yes q =
      subst (λ o' → wkᵉⁿ-H k (wkᵉ-H Q) ⊩ᵒ o' [ (δ ↑ᵉ) ↑ᵉⁿ k ]) q
            (⊩ᵒ-subst⁻ (⊩ᵒ-resp-≐ˢ eq (⊩ᵒ-⨟ (⊩ᴴ-↑ᵉⁿ k ⊩ᴴ-wkᵉ) h)))
  where
    eq : ((δ ↑ᵉⁿ k) ⨟ˢ (wkˢᵉ ↑ᵉⁿ k)) ≐ˢ ((wkˢᵉ ↑ᵉⁿ k) ⨟ˢ ((δ ↑ᵉ) ↑ᵉⁿ k))
    eq = ≐ˢ-trans (⨟-↑ᵉⁿ δ wkˢᵉ k)
         (≐ˢ-trans (≐ˢ-↑ᵉⁿ (≐ˢ-sym (wkˢᵉ-↑ᵉ δ)) k) (≐ˢ-sym (⨟-↑ᵉⁿ wkˢᵉ (δ ↑ᵉ) k)))

closeᵈ-princ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (E : Dfr (Ψ +e))
             → wkᵉ-H Q ⊩ᵈ E [ δ ↑ᵉ ] → Q ⊩ᵈ closeᵈ E [ δ ]
closeᵈ-princ {Q = Q} {δ} (dfr l k o) h with o [ κ⟨ ûₑ ⟩ ↑ᵉⁿ k ]ᴼ [ wkˢᵉ ↑ᵉⁿ k ]ᴼ ≟ᴼ o
... | no _  = h
... | yes _ = ⊩ᵒ-subst⁻ (⊩ᵒ-resp-≐ˢ eq (⊩ᵒ-⨟ (⊩ᴴ-↑ᵉⁿ k (⊩ᴴ-κ ûₑ)) h))
  where
    eq : (((δ ↑ᵉ) ↑ᵉⁿ k) ⨟ˢ (κ⟨ ûₑ ⟩ ↑ᵉⁿ k)) ≐ˢ ((κ⟨ ûₑ ⟩ ↑ᵉⁿ k) ⨟ˢ (δ ↑ᵉⁿ k))
    eq = ≐ˢ-trans (⨟-↑ᵉⁿ (δ ↑ᵉ) κ⟨ ûₑ ⟩ k)
         (≐ˢ-trans (≐ˢ-↑ᵉⁿ (↑-κ δ uₑ) k) (≐ˢ-sym (⨟-↑ᵉⁿ κ⟨ ûₑ ⟩ δ k)))
