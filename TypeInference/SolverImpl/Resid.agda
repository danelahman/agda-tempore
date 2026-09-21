------------------------------------------------------------------
-- Residual constraints                                           --
--                                                                --
-- A `Resid Ψ` is the list of grade orderings, eternality         --
-- demands, subtyping demands and var-rule disjunctions the       --
-- driver has left open over the current scope. Unlike `Hyps`, a  --
-- residual is closed under substitution, which is what lets the  --
-- driver push it through the store extensions a unification      --
-- performs.                                                      --
--                                                                --
-- `Q ⊩ᴿ R [ δ ]` discharges a residual: every atom, instantiated --
-- along `δ`, is entailed by `Q`. `toHyps` reads a residual back  --
-- as a hypothesis set, decomposing the eternality demands        --
-- (`etDec`) and the subtyping demands (`subDec`) into atoms on   --
-- type variables and taking the rest verbatim. `subDec` stops at --
-- a pair of type variables; a type variable against a former has --
-- no decomposition.                                              --
--                                                                --
-- The name follows OutsideIn(X) (Vytiniotis et al., JFP 2011).   --
------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Maybe.Base using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Resid (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (EternalBaseType; eternalBaseType?; _≡ᵇ?_)

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.SolverImpl.Core.Rigid S using (zip₂; zip₂-just)

record Resid (Ψ : Scope) : Set where
  constructor resid
  field
    rs : List (RExp Ψ × RExp Ψ)            -- open resource-grade orderings
    es : List (EExp Ψ × EExp Ψ)            -- open effect-grade orderings
    ts : List (OVType Ψ)                   -- open eternality demands
    ss : List (OVType Ψ × OVType Ψ)        -- open subtyping demands
    ds : List (OVType Ψ × RExp Ψ)          -- open var-rule disjunctions

open Resid public

emptyᴿ : ∀ {Ψ} → Resid Ψ
emptyᴿ = resid [] [] [] [] []

infixl 50 _[_]ᴿ
infixr 5 _∪ᴿ_

_[_]ᴿ : ∀ {Ψ Ψ'} → Resid Ψ → Subst Ψ Ψ' → Resid Ψ'
R [ σ ]ᴿ = resid (map (mapᵖ (_[ σ ]ʳ)) (rs R))
                 (map (mapᵖ (_[ σ ]ᵉ)) (es R))
                 (map (_[ σ ]ᵛ) (ts R))
                 (map (mapᵖ (_[ σ ]ᵛ)) (ss R))
                 (map (mapᵈ (_[ σ ]ᵛ) (_[ σ ]ʳ)) (ds R))

_∪ᴿ_ : ∀ {Ψ} → Resid Ψ → Resid Ψ → Resid Ψ
R ∪ᴿ R' = resid (rs R ++ rs R') (es R ++ es R') (ts R ++ ts R')
                (ss R ++ ss R') (ds R ++ ds R')

-- Pushing one atom

pushʳ : ∀ {Ψ} → RExp Ψ → RExp Ψ → Resid Ψ → Resid Ψ
pushʳ ρ ρ' R = resid ((ρ , ρ') ∷ rs R) (es R) (ts R) (ss R) (ds R)

pushᵉ : ∀ {Ψ} → EExp Ψ → EExp Ψ → Resid Ψ → Resid Ψ
pushᵉ ε ε' R = resid (rs R) ((ε , ε') ∷ es R) (ts R) (ss R) (ds R)

pushᵗ : ∀ {Ψ} → OVType Ψ → Resid Ψ → Resid Ψ
pushᵗ A R = resid (rs R) (es R) (A ∷ ts R) (ss R) (ds R)

pushᵈ : ∀ {Ψ} → OVType Ψ → RExp Ψ → Resid Ψ → Resid Ψ
pushᵈ A ρ R = resid (rs R) (es R) (ts R) (ss R) ((A , ρ) ∷ ds R)

infix 4 _⊩ᴿ_[_]

record _⊩ᴿ_[_] {Ψ Ψ' : Scope} (Q : Hyps Ψ') (R : Resid Ψ) (δ : Subst Ψ Ψ') : Set where
  constructor mk⊩ᴿ
  field
    ⊩rs : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    ⊩es : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
    ⊩ts : ∀ {A}    → A ∈ ts R        → Q ⊩ᴱ A [ δ ]ᵛ
    ⊩ss : ∀ {A B}  → (A , B) ∈ ss R  → Q ∣ A [ δ ]ᵛ <:̂ᵛ B [ δ ]ᵛ
    ⊩ds : ∀ {A ρ}  → (A , ρ) ∈ ds R  → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ)

open _⊩ᴿ_[_] public

⊩ᴿ-empty : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → Q ⊩ᴿ emptyᴿ [ δ ]
⊩ᴿ-empty = mk⊩ᴿ (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

⊩ᴿ-resp-≐ˢ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {δ δ' : Subst Ψ Ψ'}
           → δ ≐ˢ δ' → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ R [ δ' ]
⊩ᴿ-resp-≐ˢ {Q = Q} p h =
  mk⊩ᴿ (λ {ρ} {ρ'} m → subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([≐]ʳ p ρ) ([≐]ʳ p ρ') (⊩rs h m))
       (λ {ε} {ε'} m → subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([≐]ᵉ p ε) ([≐]ᵉ p ε') (⊩es h m))
       (λ {A}       m → subst (Q ⊩ᴱ_) ([≐]ᵛ p A) (⊩ts h m))
       (λ {A} {B}   m → subst₂ (Q ∣_<:̂ᵛ_) ([≐]ᵛ p A) ([≐]ᵛ p B) (⊩ss h m))
       (λ {A} {ρ}   m → subst₂ (VarOK Q) ([≐]ᵛ p A) ([≐]ʳ p ρ) (⊩ds h m))

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
       (λ {A} {B}  m → subst₂ (Q ∣_<:̂ᵛ_) ([⨟]ᵛ A σ δ) ([⨟]ᵛ B σ δ)
                              (⊩ss h (∈-map⁺ (mapᵖ (_[ σ ]ᵛ)) m)))
       (λ {A} {ρ}  m → subst₂ (VarOK Q) ([⨟]ᵛ A σ δ) ([⨟]ʳ ρ σ δ)
                              (⊩ds h (∈-map⁺ (mapᵈ (_[ σ ]ᵛ) (_[ σ ]ʳ)) m)))

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
       (λ {A} {B}  m → subst₂ (Q' ∣_<:̂ᵛ_) ([⨟]ᵛ A δ δ') ([⨟]ᵛ B δ δ')
                              (<:̂ᵛ-subst g (⊩ss h m)))
       (λ {A} {ρ}  m → subst₂ (VarOK Q') ([⨟]ᵛ A δ δ') ([⨟]ʳ ρ δ δ')
                              (VarOK-subst g (⊩ds h m)))

-- The two components of a union

∪ᴿ-fst : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R R' : Resid Ψ} {δ : Subst Ψ Ψ'}
       → Q ⊩ᴿ (R ∪ᴿ R') [ δ ] → Q ⊩ᴿ R [ δ ]
∪ᴿ-fst h = mk⊩ᴿ (λ m → ⊩rs h (∈-++⁺ˡ m))
                (λ m → ⊩es h (∈-++⁺ˡ m))
                (λ m → ⊩ts h (∈-++⁺ˡ m))
                (λ m → ⊩ss h (∈-++⁺ˡ m))
                (λ m → ⊩ds h (∈-++⁺ˡ m))

∪ᴿ-snd : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R R' : Resid Ψ} {δ : Subst Ψ Ψ'}
       → Q ⊩ᴿ (R ∪ᴿ R') [ δ ] → Q ⊩ᴿ R' [ δ ]
∪ᴿ-snd {R = R} h = mk⊩ᴿ (λ m → ⊩rs h (∈-++⁺ʳ (rs R) m))
                        (λ m → ⊩es h (∈-++⁺ʳ (es R) m))
                        (λ m → ⊩ts h (∈-++⁺ʳ (ts R) m))
                        (λ m → ⊩ss h (∈-++⁺ʳ (ss R) m))
                        (λ m → ⊩ds h (∈-++⁺ʳ (ds R) m))

-- The tail of a residual with one atom pushed

tailʳ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {ρ ρ' : RExp Ψ} {δ : Subst Ψ Ψ'}
      → Q ⊩ᴿ (pushʳ ρ ρ' R) [ δ ] → Q ⊩ᴿ R [ δ ]
tailʳ h = mk⊩ᴿ (λ m → ⊩rs h (there m)) (⊩es h) (⊩ts h) (⊩ss h) (⊩ds h)

tailᵉ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {ε ε' : EExp Ψ} {δ : Subst Ψ Ψ'}
      → Q ⊩ᴿ (pushᵉ ε ε' R) [ δ ] → Q ⊩ᴿ R [ δ ]
tailᵉ h = mk⊩ᴿ (⊩rs h) (λ m → ⊩es h (there m)) (⊩ts h) (⊩ss h) (⊩ds h)

tailᵗ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {A : OVType Ψ} {δ : Subst Ψ Ψ'}
      → Q ⊩ᴿ (pushᵗ A R) [ δ ] → Q ⊩ᴿ R [ δ ]
tailᵗ h = mk⊩ᴿ (⊩rs h) (⊩es h) (λ m → ⊩ts h (there m)) (⊩ss h) (⊩ds h)

tailᵈ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {A : OVType Ψ} {ρ : RExp Ψ}
          {δ : Subst Ψ Ψ'}
      → Q ⊩ᴿ (pushᵈ A ρ R) [ δ ] → Q ⊩ᴿ R [ δ ]
tailᵈ h = mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (⊩ss h) (λ m → ⊩ds h (there m))

-- The empty hypothesis set entails nothing, so every decision taken
-- against it transports to any hypothesis set and any substitution

∅ᴴ-⊩ᴴ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → Q ⊩ᴴ ∅ᴴ [ δ ]
∅ᴴ-⊩ᴴ = mk⊩ᴴ (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

-- The atoms a subtyping demand decomposes to: pairs of type
-- variables and the grade orderings of the slots passed through.

record SubAtoms (Ψ : Scope) : Set where
  constructor atoms
  field
    asubᵥ : List (TyVar Ψ × TyVar Ψ)
    aordᵣ : List (RExp Ψ × RExp Ψ)
    aordₑ : List (EExp Ψ × EExp Ψ)

open SubAtoms public

noAtoms : ∀ {Ψ} → SubAtoms Ψ
noAtoms = atoms [] [] []

atomsᵛ : ∀ {Ψ} → TyVar Ψ → TyVar Ψ → SubAtoms Ψ
atomsᵛ α β = atoms ((α , β) ∷ []) [] []

atomsʳ : ∀ {Ψ} → RExp Ψ → RExp Ψ → SubAtoms Ψ
atomsʳ ρ ρ' = atoms [] ((ρ , ρ') ∷ []) []

atomsᵉ : ∀ {Ψ} → EExp Ψ → EExp Ψ → SubAtoms Ψ
atomsᵉ ε ε' = atoms [] [] ((ε , ε') ∷ [])

infixr 5 _∪ᴬ_

_∪ᴬ_ : ∀ {Ψ} → SubAtoms Ψ → SubAtoms Ψ → SubAtoms Ψ
a ∪ᴬ b = atoms (asubᵥ a ++ asubᵥ b) (aordᵣ a ++ aordᵣ b) (aordₑ a ++ aordₑ b)

-- The atoms hold along `δ` under `Q`

record Holds {Ψ Ψ' : Scope} (Q : Hyps Ψ') (δ : Subst Ψ Ψ') (a : SubAtoms Ψ) : Set where
  constructor holds
  field
    hv : ∀ {α β} → (α , β) ∈ asubᵥ a → Q ∣ sTy δ α <:̂ᵛ sTy δ β
    hr : ∀ {ρ ρ'} → (ρ , ρ') ∈ aordᵣ a → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    he : ∀ {ε ε'} → (ε , ε') ∈ aordₑ a → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ

open Holds public

holdsᵛ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} {α β}
       → Q ∣ sTy δ α <:̂ᵛ sTy δ β → Holds Q δ (atomsᵛ α β)
holdsᵛ p = holds (λ { (here refl) → p }) (λ ()) (λ ())

holdsʳ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} {ρ ρ'}
       → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ → Holds Q δ (atomsʳ ρ ρ')
holdsʳ p = holds (λ ()) (λ { (here refl) → p }) (λ ())

holdsᵉ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} {ε ε'}
       → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ → Holds Q δ (atomsᵉ ε ε')
holdsᵉ p = holds (λ ()) (λ ()) (λ { (here refl) → p })

∪ᴬ-intro : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} {a b}
         → Holds Q δ a → Holds Q δ b → Holds Q δ (a ∪ᴬ b)
∪ᴬ-intro {a = a} g h =
  holds (λ m → [ hv g , hv h ]′ (∈-++⁻ (asubᵥ a) m))
        (λ m → [ hr g , hr h ]′ (∈-++⁻ (aordᵣ a) m))
        (λ m → [ he g , he h ]′ (∈-++⁻ (aordₑ a) m))

∪ᴬ-fst : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (a b : SubAtoms Ψ)
       → Holds Q δ (a ∪ᴬ b) → Holds Q δ a
∪ᴬ-fst a b h = holds (λ m → hv h (∈-++⁺ˡ m)) (λ m → hr h (∈-++⁺ˡ m))
                     (λ m → he h (∈-++⁺ˡ m))

∪ᴬ-snd : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (a b : SubAtoms Ψ)
       → Holds Q δ (a ∪ᴬ b) → Holds Q δ b
∪ᴬ-snd a b h = holds (λ m → hv h (∈-++⁺ʳ (asubᵥ a) m))
                     (λ m → hr h (∈-++⁺ʳ (aordᵣ a) m))
                     (λ m → he h (∈-++⁺ʳ (aordₑ a) m))

-- The atoms as a residual of their own: the variable pairs become
-- subtyping demands between variable types.

atomsᴿ : ∀ {Ψ} → SubAtoms Ψ → Resid Ψ
atomsᴿ a = resid (aordᵣ a) (aordₑ a) [] (map (mapᵖ tvar) (asubᵥ a)) []

holdsᴿ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (a : SubAtoms Ψ)
       → Q ⊩ᴿ (atomsᴿ a) [ δ ] → Holds Q δ a
holdsᴿ a h = holds (λ m → ⊩ss h (∈-map⁺ (mapᵖ tvar) m)) (⊩rs h) (⊩es h)

atomsᴿ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (a : SubAtoms Ψ)
         → Holds Q δ a → Q ⊩ᴿ (atomsᴿ a) [ δ ]
atomsᴿ-⊩ {Q = Q} {δ = δ} a hs = mk⊩ᴿ (hr hs) (he hs) (λ ()) ss' (λ ())
  where
    ss' : ∀ {X Y} → (X , Y) ∈ map (mapᵖ tvar) (asubᵥ a) → Q ∣ X [ δ ]ᵛ <:̂ᵛ Y [ δ ]ᵛ
    ss' m with ∈-map⁻ (mapᵖ tvar) m
    ... | (α , β) , m₀ , refl = hv hs m₀

-- A decomposition carries both directions: the atoms entail the
-- demand at every instance, and every instance of the demand
-- entails them.

record SubDec {Ψ : Scope} (A B : OVType Ψ) : Set where
  constructor subdec
  field
    atomsOf : SubAtoms Ψ
    intro   : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
            → Holds Q δ atomsOf → Q ∣ A [ δ ]ᵛ <:̂ᵛ B [ δ ]ᵛ
    elim    : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
            → Q ∣ A [ δ ]ᵛ <:̂ᵛ B [ δ ]ᵛ → Holds Q δ atomsOf

open SubDec public

record SubDecᶜ {Ψ : Scope} (C D : OCType Ψ) : Set where
  constructor subdecᶜ
  field
    atomsOfᶜ : SubAtoms Ψ
    introᶜ   : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
             → Holds Q δ atomsOfᶜ → Q ∣ C [ δ ]ᶜ <:̂ᶜ D [ δ ]ᶜ
    elimᶜ    : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
             → Q ∣ C [ δ ]ᶜ <:̂ᶜ D [ δ ]ᶜ → Holds Q δ atomsOfᶜ

open SubDecᶜ public

-- One assembly per pair of matching formers

pairᴰ : ∀ {Ψ} {A A' B B' : OVType Ψ} → SubDec A A' → SubDec B B'
      → SubDec (A |×| B) (A' |×| B')
pairᴰ d e =
  subdec (atomsOf d ∪ᴬ atomsOf e)
         (λ δ h → intro d δ (∪ᴬ-fst (atomsOf d) (atomsOf e) h) |×|ₛ
                  intro e δ (∪ᴬ-snd (atomsOf d) (atomsOf e) h))
         (λ { δ (p |×|ₛ q) → ∪ᴬ-intro (elim d δ p) (elim e δ q) })

arrᴰ : ∀ {Ψ} {A A' : OVType Ψ} {C C' : OCType Ψ} → SubDec A' A → SubDecᶜ C C'
     → SubDec (A ⇒ C) (A' ⇒ C')
arrᴰ d e =
  subdec (atomsOf d ∪ᴬ atomsOfᶜ e)
         (λ δ h → intro d δ (∪ᴬ-fst (atomsOf d) (atomsOfᶜ e) h) ⇒ₛ
                  introᶜ e δ (∪ᴬ-snd (atomsOf d) (atomsOfᶜ e) h))
         (λ { δ (p ⇒ₛ q) → ∪ᴬ-intro (elim d δ p) (elimᶜ e δ q) })

boxᴰ : ∀ {Ψ} {A A' : OVType Ψ} → (ρ ρ' : RExp Ψ) → SubDec A A'
     → SubDec ([ ρ ] A) ([ ρ' ] A')
boxᴰ ρ ρ' d =
  subdec (atomsʳ ρ' ρ ∪ᴬ atomsOf d)
         (λ δ h → [ hr (∪ᴬ-fst (atomsʳ ρ' ρ) (atomsOf d) h) (here refl) ]ₛ
                  intro d δ (∪ᴬ-snd (atomsʳ ρ' ρ) (atomsOf d) h))
         (λ { δ ([ q ]ₛ p) → ∪ᴬ-intro (holdsʳ q) (elim d δ p) })

bangᴰ : ∀ {Ψ} {A A' : OVType Ψ} → (ε ε' : EExp Ψ) → SubDec A A'
      → SubDecᶜ (A ‼ ε) (A' ‼ ε')
bangᴰ ε ε' d =
  subdecᶜ (atomsOf d ∪ᴬ atomsᵉ ε ε')
          (λ δ h → intro d δ (∪ᴬ-fst (atomsOf d) (atomsᵉ ε ε') h) ‼ₛ
                   he (∪ᴬ-snd (atomsOf d) (atomsᵉ ε ε') h) (here refl))
          (λ { δ (p ‼ₛ q) → ∪ᴬ-intro (elim d δ p) (holdsᵉ q) })

leafᴰ : ∀ {Ψ} {A B : OVType Ψ}
      → (∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → Q ∣ A [ δ ]ᵛ <:̂ᵛ B [ δ ]ᵛ)
      → SubDec A B
leafᴰ f = subdec noAtoms (λ δ h → f δ) (λ δ p → holds (λ ()) (λ ()) (λ ()))

-- `_∣_<:̂ᵛ_` has one rule per pair of matching formers and `tvarₛ` at a
-- pair of type variables: a demand reduces to atoms on type variables
-- and grade orderings, or has no decomposition.

subDec  : ∀ {Ψ} → (A B : OVType Ψ) → Maybe (SubDec A B)
subDecᶜ : ∀ {Ψ} → (C D : OCType Ψ) → Maybe (SubDecᶜ C D)

subDec (tvar α) (tvar β) =
  just (subdec (atomsᵛ α β) (λ δ h → hv h (here refl)) (λ δ p → holdsᵛ p))
subDec (Base b) (Base b') with b ≡ᵇ? b'
... | yes refl = just (leafᴰ (λ δ → Baseₛ refl))
... | no _     = nothing
subDec Unit       Unit        = just (leafᴰ (λ δ → Unitₛ))
subDec Bool       Bool        = just (leafᴰ (λ δ → Boolₛ))
subDec Empty      Empty       = just (leafᴰ (λ δ → Emptyₛ))
subDec (A |×| B)  (A' |×| B') = zip₂ pairᴰ (subDec A A') (subDec B B')
subDec (A ⇒ C)    (A' ⇒ C')   = zip₂ arrᴰ (subDec A' A) (subDecᶜ C C')
subDec ([ ρ ] A)  ([ ρ' ] A') = mmap (boxᴰ ρ ρ') (subDec A A')
subDec _          _           = nothing

subDecᶜ (A ‼ ε) (A' ‼ ε') = mmap (bangᴰ ε ε') (subDec A A')

-- `_⊩ᴱ_` has one rule per former except `_⇒_` and `[_]_`, and `et-hyp`
-- at a type variable: a demand reduces to demands on type variables or
-- is refuted.

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

-- The decomposition is paired with the entailment it justifies, so
-- `etsList`'s case analysis stays visible to a proof about it.

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

-- The decomposition of a whole list of subtyping demands

record SubsDec {Ψ : Scope} (l : List (OVType Ψ × OVType Ψ)) : Set where
  constructor subsdec
  field
    atomsOfˢ : SubAtoms Ψ
    introˢ   : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → Holds Q δ atomsOfˢ
             → ∀ {A B} → (A , B) ∈ l → Q ∣ A [ δ ]ᵛ <:̂ᵛ B [ δ ]ᵛ
    elimˢ    : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
             → (∀ {A B} → (A , B) ∈ l → Q ∣ A [ δ ]ᵛ <:̂ᵛ B [ δ ]ᵛ)
             → Holds Q δ atomsOfˢ

open SubsDec public

subsList : ∀ {Ψ} → (l : List (OVType Ψ × OVType Ψ)) → Maybe (SubsDec l)
subsList []             =
  just (subsdec noAtoms (λ δ h ()) (λ δ k → holds (λ ()) (λ ()) (λ ())))
subsList ((A , B) ∷ l) with subDec A B | subsList l
... | just d  | just ds =
      just (subsdec (atomsOf d ∪ᴬ atomsOfˢ ds)
                    (λ δ h →
                       λ { (here refl) →
                             intro d δ (∪ᴬ-fst (atomsOf d) (atomsOfˢ ds) h)
                         ; (there m)   →
                             introˢ ds δ (∪ᴬ-snd (atomsOf d) (atomsOfˢ ds) h) m })
                    (λ δ k → ∪ᴬ-intro (elim d δ (k (here refl)))
                                      (elimˢ ds δ (λ m → k (there m)))))
... | just _  | nothing = nothing
... | nothing | _       = nothing

subsList-nothing : ∀ {Ψ} → (l : List (OVType Ψ × OVType Ψ)) → subsList l ≡ nothing
                 → Σ[ A ∈ OVType Ψ ] Σ[ B ∈ OVType Ψ ]
                     (((A , B) ∈ l) × (subDec A B ≡ nothing))
subsList-nothing []             ()
subsList-nothing ((A , B) ∷ l) eq with subDec A B in e₀ | subsList l in e
subsList-nothing ((A , B) ∷ l) () | just _ | just _
subsList-nothing ((A , B) ∷ l) eq | just _ | nothing with subsList-nothing l e
... | A' , B' , m , q = A' , B' , there m , q
subsList-nothing ((A , B) ∷ l) eq | nothing | _ = A , B , here refl , e₀

toHyps : ∀ {Ψ} → (R : Resid Ψ) → Maybe (Σ[ Q ∈ Hyps Ψ ] (Q ⊩ᴿ R [ idˢ ]))
toHyps R with etsList (ts R) | subsList (ss R)
... | nothing       | _       = nothing
... | just _        | nothing = nothing
... | just (αs , f) | just d  = just (Q , mk⊩ᴿ ordᵣ' ordₑ' ets' subs' disj')
  where
    a : SubAtoms _
    a = atomsOfˢ d

    Q : Hyps _
    Q = hyps αs (asubᵥ a) (rs R ++ aordᵣ a) (es R ++ aordₑ a) (ds R)

    hyps' : Holds Q idˢ a
    hyps' =
      holds (λ m → tvarₛ (hypᵗᵛ m))
            (λ {ρ} {ρ'} m →
               subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([id]ʳ ρ)) (sym ([id]ʳ ρ'))
                      (hypᵣ (∈-++⁺ʳ (rs R) m)))
            (λ {ε} {ε'} m →
               subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([id]ᵉ ε)) (sym ([id]ᵉ ε'))
                      (hypₑ (∈-++⁺ʳ (es R) m)))

    ets' : ∀ {A} → A ∈ ts R → Q ⊩ᴱ A [ idˢ ]ᵛ
    ets' {A} m = subst (Q ⊩ᴱ_) (sym ([id]ᵛ A)) (f et-hyp m)

    subs' : ∀ {A B} → (A , B) ∈ ss R → Q ∣ A [ idˢ ]ᵛ <:̂ᵛ B [ idˢ ]ᵛ
    subs' = introˢ d idˢ hyps'

    ordᵣ' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ idˢ ]ʳ ≾̂ᵣ ρ' [ idˢ ]ʳ
    ordᵣ' {ρ} {ρ'} m =
      subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([id]ʳ ρ)) (sym ([id]ʳ ρ'))
             (hypᵣ (∈-++⁺ˡ m))

    ordₑ' : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ idˢ ]ᵉ ≾̂ₑ ε' [ idˢ ]ᵉ
    ordₑ' {ε} {ε'} m =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([id]ᵉ ε)) (sym ([id]ᵉ ε'))
             (hypₑ (∈-++⁺ˡ m))

    disj' : ∀ {A ρ} → (A , ρ) ∈ ds R → VarOK Q (A [ idˢ ]ᵛ) (ρ [ idˢ ]ʳ)
    disj' {A} {ρ} m =
      subst₂ (VarOK Q) (sym ([id]ᵛ A)) (sym ([id]ʳ ρ)) (hyp-ok m)

-- The same, for a whole residual

toHyps-nothing : ∀ {Ψ} → (R : Resid Ψ) → toHyps R ≡ nothing
               → Σ[ A ∈ OVType Ψ ] ((A ∈ ts R) × (etDec A ≡ nothing))
               ⊎ Σ[ A ∈ OVType Ψ ] Σ[ B ∈ OVType Ψ ]
                   (((A , B) ∈ ss R) × (subDec A B ≡ nothing))
toHyps-nothing R eq with etsList (ts R) in e | subsList (ss R) in e'
... | nothing | _       = inj₁ (etsList-nothing (ts R) e)
... | just _  | nothing = inj₂ (subsList-nothing (ss R) e')
toHyps-nothing R () | just _ | just _

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
toHyps-compl R eq δ h with etsList (ts R) in e | subsList (ss R) in e'
toHyps-compl R () δ h | nothing        | _
toHyps-compl R () δ h | just _         | nothing
toHyps-compl R eq δ h | just (αs , f)  | just d with eq
... | refl = mk⊩ᴴ (etsList-compl (ts R) e δ (⊩ts h)) (hv hs) ordᵣ' ordₑ' (⊩ds h)
  where
    hs : Holds _ δ (atomsOfˢ d)
    hs = elimˢ d δ (⊩ss h)

    ordᵣ' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R ++ aordᵣ (atomsOfˢ d)
          → _ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    ordᵣ' m = [ ⊩rs h , hr hs ]′ (∈-++⁻ (rs R) m)

    ordₑ' : ∀ {ε ε'} → (ε , ε') ∈ es R ++ aordₑ (atomsOfˢ d)
          → _ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
    ordₑ' m = [ ⊩es h , he hs ]′ (∈-++⁻ (es R) m)
