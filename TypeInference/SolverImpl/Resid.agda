------------------------------------------------------------------
-- Residual constraints                                         --
--                                                              --
-- A `Resid Ψ` is the list of grade orderings, eternality       --
-- demands, subtyping demands and var-rule disjunctions that    --
-- the driver leaves open over the current scope, together with --
-- the deferred rigid conditions of the clauses closed so far   --
-- (`Deferred`). A residual, unlike a `Hyps`, is closed under   --
-- substitution; the driver pushes it through the substitutions --
-- of an expansion and of a scope's close.                      --
--                                                              --
-- Its eternality demands are on type variables: a demand is    --
-- decomposed by `etDec` when it is pushed, and again after     --
-- each expansion (`atomiseᴿ`), which may instantiate its       --
-- variables.                                                   --
--                                                              --
-- `Q ⊩ᴿ R [ δ ]` discharges a residual: `Q` entails every atom --
-- and every deferred condition, instantiated along `δ`.        --
-- `toHyps` reads the atoms back as a hypothesis set,           --
-- decomposing the eternality demands (`etsDec`) and the        --
-- subtyping demands (`subDec`) into atoms on type variables    --
-- and keeping the rest unchanged. `subDec` and `etDec` read    --
-- the variance table and its eternality column (`Former`),     --
-- by recursion on the parts of a type. `subDec` stops at a     --
-- pair of type variables; a type variable against a former,    --
-- or two clashing formers, have no decomposition.              --
--                                                              --
-- Contract. A decomposition `subDec A B` is exact (`Exact`) at --
-- every instance and under any hypotheses: its atoms entail    --
-- the demand (`intro`) and are entailed by it (`elim`), and    --
-- likewise for a list (`subsList`: `introˢ`/`elimˢ`). A        --
-- failure claims nothing by itself; after an expansion none    --
-- occurs (`expandSub-dec`, `reexpand-dec`), as `subDec`        --
-- succeeds on the pairs of a symmetric relation that pairs     --
-- types of one former part by part (`SubDecJust`). `etDec` is  --
-- exact likewise (`etDec-intro`, `etDec-compl`; for a list,    --
-- `etsDec`: `introᵗ`/`elimᵗ`); its failure refutes the demand  --
-- at every instance (`etDec-refute`) and reduces a disjunction --
-- to its grade side (`etDec-grade`). `atomiseᴿ` has the same   --
-- instances as the original, in both directions                --
-- (`atomiseᴿ-sound`, `atomiseᴿ-compl`). `toHyps R` entails the --
-- atoms of `R` (by its type), is entailed by them at every     --
-- instance (`toHyps-compl`), and fails only on a demand on     --
-- which `subDec` or `etDec` fails (`toHyps-nothing`).          --
--                                                              --
-- The name follows OutsideIn(X) (Vytiniotis et al., JFP 2011). --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false)
open import Data.List.Base using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup; tabulate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Empty.Irrelevant renaming (⊥-elim to ⊥-elim-irr)
open import Data.Maybe.Base using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)

open import Induction.WellFounded using (Acc; acc; WfRec)

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

open import TypeInference.SolverImpl.Core.Rigid S using (zip₂; zip₂-just; zip₂-nothing; strᵛ)
open import TypeInference.SolverImpl.Former     S
open import TypeInference.SolverImpl.Deferred   S
  using (Dfr; _[_]ᵈ; _⊩ᵈ_[_]; ⊩ᵈ-resp-≐ˢ; ⊩ᵈ-subst; ⊩ᵈ-subst⁻; ⊩ᵈ-⨟)

record Resid (Ψ : Scope) : Set where
  constructor resid
  field
    rs : List (RExp Ψ × RExp Ψ)            -- open resource-grade orderings
    es : List (EExp Ψ × EExp Ψ)            -- open effect-grade orderings
    ts : List (OVType Ψ)                   -- open eternality demands, on type variables
    ss : List (OVType Ψ × OVType Ψ)        -- open subtyping demands
    ds : List (OVType Ψ × RExp Ψ)          -- open var-rule disjunctions
    dfs : List (Dfr Ψ)                     -- deferred rigid conditions

open Resid public

emptyᴿ : ∀ {Ψ} → Resid Ψ
emptyᴿ = resid [] [] [] [] [] []

infixl 50 _[_]ᴿ
infixr 5 _∪ᴿ_

_[_]ᴿ : ∀ {Ψ Ψ'} → Resid Ψ → Subst Ψ Ψ' → Resid Ψ'
R [ σ ]ᴿ = resid (map (mapᵖ (_[ σ ]ʳ)) (rs R))
                 (map (mapᵖ (_[ σ ]ᵉ)) (es R))
                 (map (_[ σ ]ᵛ) (ts R))
                 (map (mapᵖ (_[ σ ]ᵛ)) (ss R))
                 (map (mapᵈ (_[ σ ]ᵛ) (_[ σ ]ʳ)) (ds R))
                 (map (_[ σ ]ᵈ) (dfs R))

-- Subtyping demands that are pairs of type variables, which a
-- substitution fixing every type variable keeps

Atomicˢ : ∀ {Ψ} → List (OVType Ψ × OVType Ψ) → Set
Atomicˢ {Ψ} l = ∀ {A B} → (A , B) ∈ l
              → Σ[ α ∈ TyVar Ψ ] Σ[ β ∈ TyVar Ψ ] ((A ≡ tvar α) × (B ≡ tvar β))

atomic-subst : ∀ {Ψ} → (σ : Subst Ψ Ψ) → (∀ α → sTy σ α ≡ tvar α)
             → {l : List (OVType Ψ × OVType Ψ)} → Atomicˢ l
             → Atomicˢ (map (mapᵖ (_[ σ ]ᵛ)) l)
atomic-subst σ fx at m with ∈-map⁻ (mapᵖ (_[ σ ]ᵛ)) m
... | (A , B) , m₀ , refl with at m₀
...   | α , β , refl , refl = α , β , fx α , fx β

_∪ᴿ_ : ∀ {Ψ} → Resid Ψ → Resid Ψ → Resid Ψ
R ∪ᴿ R' = resid (rs R ++ rs R') (es R ++ es R') (ts R ++ ts R')
                (ss R ++ ss R') (ds R ++ ds R') (dfs R ++ dfs R')

-- Pushing one atom

pushʳ : ∀ {Ψ} → RExp Ψ → RExp Ψ → Resid Ψ → Resid Ψ
pushʳ ρ ρ' R = resid ((ρ , ρ') ∷ rs R) (es R) (ts R) (ss R) (ds R) (dfs R)

pushᵉ : ∀ {Ψ} → EExp Ψ → EExp Ψ → Resid Ψ → Resid Ψ
pushᵉ ε ε' R = resid (rs R) ((ε , ε') ∷ es R) (ts R) (ss R) (ds R) (dfs R)

pushᵗ : ∀ {Ψ} → List (TyVar Ψ) → Resid Ψ → Resid Ψ
pushᵗ αs R = resid (rs R) (es R) (map tvar αs ++ ts R) (ss R) (ds R) (dfs R)

pushᵈ : ∀ {Ψ} → OVType Ψ → RExp Ψ → Resid Ψ → Resid Ψ
pushᵈ A ρ R = resid (rs R) (es R) (ts R) (ss R) ((A , ρ) ∷ ds R) (dfs R)

infix 4 _⊩ᴿ_[_]

record _⊩ᴿ_[_] {Ψ Ψ' : Scope} (Q : Hyps Ψ') (R : Resid Ψ) (δ : Subst Ψ Ψ') : Set where
  constructor mk⊩ᴿ
  field
    ⊩rs : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    ⊩es : ∀ {ε ε'} → (ε , ε') ∈ es R → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
    ⊩ts : ∀ {A}    → A ∈ ts R        → Q ⊩ᴱ A [ δ ]ᵛ
    ⊩ss : ∀ {A B}  → (A , B) ∈ ss R  → Q ∣ A [ δ ]ᵛ <:̂ᵛ B [ δ ]ᵛ
    ⊩ds : ∀ {A ρ}  → (A , ρ) ∈ ds R  → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ)
    ⊩dfs : ∀ {E}   → E ∈ dfs R       → Q ⊩ᵈ E [ δ ]

open _⊩ᴿ_[_] public

⊩ᴿ-empty : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → Q ⊩ᴿ emptyᴿ [ δ ]
⊩ᴿ-empty = mk⊩ᴿ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

⊩ᴿ-resp-≐ˢ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {δ δ' : Subst Ψ Ψ'}
           → δ ≐ˢ δ' → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ R [ δ' ]
⊩ᴿ-resp-≐ˢ {Q = Q} p h =
  mk⊩ᴿ (λ {ρ} {ρ'} m → subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) ([≐]ʳ p ρ) ([≐]ʳ p ρ') (⊩rs h m))
       (λ {ε} {ε'} m → subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) ([≐]ᵉ p ε) ([≐]ᵉ p ε') (⊩es h m))
       (λ {A}       m → subst (Q ⊩ᴱ_) ([≐]ᵛ p A) (⊩ts h m))
       (λ {A} {B}   m → subst₂ (Q ∣_<:̂ᵛ_) ([≐]ᵛ p A) ([≐]ᵛ p B) (⊩ss h m))
       (λ {A} {ρ}   m → subst₂ (VarOK Q) ([≐]ᵛ p A) ([≐]ʳ p ρ) (⊩ds h m))
       (λ {E}       m → ⊩ᵈ-resp-≐ˢ E p (⊩dfs h m))

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
       (λ {E}      m → ⊩ᵈ-subst E (⊩dfs h (∈-map⁺ (_[ σ ]ᵈ) m)))

-- The converse of `⊩ᴿ-subst`

⊩ᴿ-subst⁻ : ∀ {Ψ Ψ₁ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ}
              {σ : Subst Ψ Ψ₁} {δ : Subst Ψ₁ Ψ'}
          → Q ⊩ᴿ R [ σ ⨟ˢ δ ] → Q ⊩ᴿ (R [ σ ]ᴿ) [ δ ]
⊩ᴿ-subst⁻ {Q = Q} {R = R} {σ = σ} {δ = δ} h = mk⊩ᴿ rs' es' ts' ss' ds' dfs'
  where
    rs' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs (R [ σ ]ᴿ) → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    rs' m with ∈-map⁻ (mapᵖ (_[ σ ]ʳ)) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ (λ x y → Q ⊩ x ≾̂ᵣ y) (sym ([⨟]ʳ ρ₀ σ δ)) (sym ([⨟]ʳ ρ₀' σ δ)) (⊩rs h m₀)

    es' : ∀ {ε ε'} → (ε , ε') ∈ es (R [ σ ]ᴿ) → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
    es' m with ∈-map⁻ (mapᵖ (_[ σ ]ᵉ)) m
    ... | (ε₀ , ε₀') , m₀ , refl =
      subst₂ (λ x y → Q ⊩ x ≾̂ₑ y) (sym ([⨟]ᵉ ε₀ σ δ)) (sym ([⨟]ᵉ ε₀' σ δ)) (⊩es h m₀)

    ts' : ∀ {A} → A ∈ ts (R [ σ ]ᴿ) → Q ⊩ᴱ A [ δ ]ᵛ
    ts' m with ∈-map⁻ (_[ σ ]ᵛ) m
    ... | A₀ , m₀ , refl = subst (Q ⊩ᴱ_) (sym ([⨟]ᵛ A₀ σ δ)) (⊩ts h m₀)

    ss' : ∀ {A B} → (A , B) ∈ ss (R [ σ ]ᴿ) → Q ∣ A [ δ ]ᵛ <:̂ᵛ B [ δ ]ᵛ
    ss' m with ∈-map⁻ (mapᵖ (_[ σ ]ᵛ)) m
    ... | (A₀ , B₀) , m₀ , refl =
      subst₂ (Q ∣_<:̂ᵛ_) (sym ([⨟]ᵛ A₀ σ δ)) (sym ([⨟]ᵛ B₀ σ δ)) (⊩ss h m₀)

    ds' : ∀ {A ρ} → (A , ρ) ∈ ds (R [ σ ]ᴿ) → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ)
    ds' m with ∈-map⁻ (mapᵈ (_[ σ ]ᵛ) (_[ σ ]ʳ)) m
    ... | (A₀ , ρ₀) , m₀ , refl =
      subst₂ (VarOK Q) (sym ([⨟]ᵛ A₀ σ δ)) (sym ([⨟]ʳ ρ₀ σ δ)) (⊩ds h m₀)

    dfs' : ∀ {E} → E ∈ dfs (R [ σ ]ᴿ) → Q ⊩ᵈ E [ δ ]
    dfs' m with ∈-map⁻ (_[ σ ]ᵈ) m
    ... | E₀ , m₀ , refl = ⊩ᵈ-subst⁻ E₀ (⊩dfs h m₀)

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
       (λ {E}      m → ⊩ᵈ-⨟ E g (⊩dfs h m))

-- The two components of a union

∪ᴿ-fst : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R R' : Resid Ψ} {δ : Subst Ψ Ψ'}
       → Q ⊩ᴿ (R ∪ᴿ R') [ δ ] → Q ⊩ᴿ R [ δ ]
∪ᴿ-fst h = mk⊩ᴿ (λ m → ⊩rs h (∈-++⁺ˡ m))
                (λ m → ⊩es h (∈-++⁺ˡ m))
                (λ m → ⊩ts h (∈-++⁺ˡ m))
                (λ m → ⊩ss h (∈-++⁺ˡ m))
                (λ m → ⊩ds h (∈-++⁺ˡ m))
                (λ m → ⊩dfs h (∈-++⁺ˡ m))

∪ᴿ-snd : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R R' : Resid Ψ} {δ : Subst Ψ Ψ'}
       → Q ⊩ᴿ (R ∪ᴿ R') [ δ ] → Q ⊩ᴿ R' [ δ ]
∪ᴿ-snd {R = R} h = mk⊩ᴿ (λ m → ⊩rs h (∈-++⁺ʳ (rs R) m))
                        (λ m → ⊩es h (∈-++⁺ʳ (es R) m))
                        (λ m → ⊩ts h (∈-++⁺ʳ (ts R) m))
                        (λ m → ⊩ss h (∈-++⁺ʳ (ss R) m))
                        (λ m → ⊩ds h (∈-++⁺ʳ (ds R) m))
                        (λ m → ⊩dfs h (∈-++⁺ʳ (dfs R) m))

-- The tail of a residual with one atom pushed

tailʳ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {ρ ρ' : RExp Ψ} {δ : Subst Ψ Ψ'}
      → Q ⊩ᴿ (pushʳ ρ ρ' R) [ δ ] → Q ⊩ᴿ R [ δ ]
tailʳ h = mk⊩ᴿ (λ m → ⊩rs h (there m)) (⊩es h) (⊩ts h) (⊩ss h) (⊩ds h) (⊩dfs h)

tailᵉ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {ε ε' : EExp Ψ} {δ : Subst Ψ Ψ'}
      → Q ⊩ᴿ (pushᵉ ε ε' R) [ δ ] → Q ⊩ᴿ R [ δ ]
tailᵉ h = mk⊩ᴿ (⊩rs h) (λ m → ⊩es h (there m)) (⊩ts h) (⊩ss h) (⊩ds h) (⊩dfs h)

tailᵗ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {αs : List (TyVar Ψ)} {δ : Subst Ψ Ψ'}
      → Q ⊩ᴿ (pushᵗ αs R) [ δ ] → Q ⊩ᴿ R [ δ ]
tailᵗ {αs = αs} h =
  mk⊩ᴿ (⊩rs h) (⊩es h) (λ m → ⊩ts h (∈-++⁺ʳ (map tvar αs) m)) (⊩ss h) (⊩ds h) (⊩dfs h)

tailᵈ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {A : OVType Ψ} {ρ : RExp Ψ}
          {δ : Subst Ψ Ψ'}
      → Q ⊩ᴿ (pushᵈ A ρ R) [ δ ] → Q ⊩ᴿ R [ δ ]
tailᵈ h = mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (⊩ss h) (λ m → ⊩ds h (there m)) (⊩dfs h)

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
atomsᴿ a = resid (aordᵣ a) (aordₑ a) [] (map (mapᵖ tvar) (asubᵥ a)) [] []

holdsᴿ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (a : SubAtoms Ψ)
       → Q ⊩ᴿ (atomsᴿ a) [ δ ] → Holds Q δ a
holdsᴿ a h = holds (λ m → ⊩ss h (∈-map⁺ (mapᵖ tvar) m)) (⊩rs h) (⊩es h)

atomsᴿ-⊩ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (a : SubAtoms Ψ)
         → Holds Q δ a → Q ⊩ᴿ (atomsᴿ a) [ δ ]
atomsᴿ-⊩ {Q = Q} {δ = δ} a hs = mk⊩ᴿ (hr hs) (he hs) (λ ()) ss' (λ ()) (λ ())
  where
    ss' : ∀ {X Y} → (X , Y) ∈ map (mapᵖ tvar) (asubᵥ a) → Q ∣ X [ δ ]ᵛ <:̂ᵛ Y [ δ ]ᵛ
    ss' m with ∈-map⁻ (mapᵖ tvar) m
    ... | (α , β) , m₀ , refl = hv hs m₀

-- An exact decomposition of a demand: atoms that entail it at every
-- instance (`intro`) and that every instance of it entails (`elim`)

record Exact {Ψ : Scope} (P : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → Set) : Set where
  constructor exact
  field
    atomsOf : SubAtoms Ψ
    intro   : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → Holds Q δ atomsOf → P Q δ
    elim    : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ') → P Q δ → Holds Q δ atomsOf

open Exact public

SubDec : ∀ {Ψ} → OVType Ψ → OVType Ψ → Set
SubDec A B = Exact (λ Q δ → Q ∣ A [ δ ]ᵛ <:̂ᵛ B [ δ ]ᵛ)

-- The demand of a pair of parts (`Former`)

PartDec : ∀ {Ψ} → Part Ψ → Set
PartDec p = Exact (λ Q δ → Holdsᴾ Q (p [ δ ∣ δ ]ᴾ))

-- Exact decompositions combine: a conjunction, a demand at a variance
-- from the decompositions of the demand and its converse, and the
-- demands of every member of a list

infixr 4 _∧ᴱ_

_∧ᴱ_ : ∀ {Ψ} {P P' : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → Set}
     → Exact P → Exact P' → Exact (λ Q δ → P Q δ × P' Q δ)
d ∧ᴱ e = exact (atomsOf d ∪ᴬ atomsOf e)
               (λ δ h → intro d δ (∪ᴬ-fst (atomsOf d) (atomsOf e) h) ,
                        intro e δ (∪ᴬ-snd (atomsOf d) (atomsOf e) h))
               (λ { δ (p , q) → ∪ᴬ-intro (elim d δ p) (elim e δ q) })

atVarᴱ : ∀ {Ψ} {P P' : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → Set} → (v : Variance)
       → Maybe (Exact P) → Maybe (Exact P') → Maybe (Exact (λ Q δ → Var v (P Q δ) (P' Q δ)))
atVarᴱ co     d e = d
atVarᴱ contra d e = e
atVarᴱ inv    d e = zip₂ _∧ᴱ_ d e

allᴱ : ∀ {Ψ} {X : Set} (R : X → ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → Set) → (xs : List X)
     → (∀ {x} → x ∈ xs → Maybe (Exact (R x)))
     → Maybe (Exact (λ Q δ → All (λ x → R x Q δ) xs))
allᴱ R []       f = just (exact noAtoms (λ δ h → []) (λ δ _ → holds (λ ()) (λ ()) (λ ())))
allᴱ R (x ∷ xs) f = zip₂ cons (f (here refl)) (allᴱ R xs (λ m → f (there m)))
  where
    cons : Exact (R x) → Exact (λ Q δ → All (λ x → R x Q δ) xs)
         → Exact (λ Q δ → All (λ x → R x Q δ) (x ∷ xs))
    cons d e = exact (atomsOf d ∪ᴬ atomsOf e)
                     (λ δ h → intro d δ (∪ᴬ-fst (atomsOf d) (atomsOf e) h) ∷
                              intro e δ (∪ᴬ-snd (atomsOf d) (atomsOf e) h))
                     (λ { δ (p ∷ ps) → ∪ᴬ-intro (elim d δ p) (elim e δ ps) })

ordʳᴱ : ∀ {Ψ} → (ρ ρ' : RExp Ψ) → Exact (λ Q δ → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ)
ordʳᴱ ρ ρ' = exact (atomsʳ ρ ρ') (λ δ h → hr h (here refl)) (λ δ p → holdsʳ p)

ordᵉᴱ : ∀ {Ψ} → (ε ε' : EExp Ψ) → Exact (λ Q δ → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ)
ordᵉᴱ ε ε' = exact (atomsᵉ ε ε') (λ δ h → he h (here refl)) (λ δ p → holdsᵉ p)

-- Two types of one former decompose as their parts do (`<:-intro`,
-- `<:-elim`)

fromParts : ∀ {Ψ} {A B : OVType Ψ} {ps} → Decomp A B ps
          → Exact (λ Q δ → All (λ p → Holdsᴾ Q (p [ δ ∣ δ ]ᴾ)) ps) → SubDec A B
fromParts g d = exact (atomsOf d) (λ δ h → <:-intro g δ δ (intro d δ h))
                      (λ δ p → elim d δ (<:-elim g δ δ p))

-- A demand reduces along the variance table to atoms on pairs of type
-- variables and grade orderings, or has no decomposition: a type
-- variable against a former, or two formers that clash. The recursion
-- is on the parts (`≺-wf`).

subDecᵃ : ∀ {Ψ} → (A B : OVType Ψ) → Acc _≺_ A → Acc _≺_ B → Maybe (SubDec A B)
partDec : ∀ {Ψ} {A B : OVType Ψ} {ps} → Decomp A B ps
        → WfRec _≺_ (Acc _≺_) A → WfRec _≺_ (Acc _≺_) B
        → ∀ {p} → p ∈ ps → Maybe (PartDec p)

subDecᵃ A B (acc ra) (acc rb) with decompose A B
... | vars α β   = just (exact (atomsᵛ α β) (λ δ h → hv h (here refl)) (λ δ p → holdsᵛ p))
... | parts ps g = mmap (fromParts g) (allᴱ (λ p Q δ → Holdsᴾ Q (p [ δ ∣ δ ]ᴾ)) ps
                                            (partDec g ra rb))
... | clash      = nothing

partDec g ra rb {ty v X Y}  m = atVarᴱ v (subDecᵃ X Y (ra (left g m)) (rb (right g m)))
                                         (subDecᵃ Y X (rb (right g m)) (ra (left g m)))
partDec g ra rb {rg v ρ ρ'} m = atVarᴱ v (just (ordʳᴱ ρ ρ')) (just (ordʳᴱ ρ' ρ))
partDec g ra rb {eg v ε ε'} m = atVarᴱ v (just (ordᵉᴱ ε ε')) (just (ordᵉᴱ ε' ε))

subDec : ∀ {Ψ} → (A B : OVType Ψ) → Maybe (SubDec A B)
subDec A B = subDecᵃ A B (≺-wf A) (≺-wf B)

-- `subDec` succeeds on every pair of a symmetric relation that relates
-- only pairs of type variables and types of one former whose
-- value-type parts it relates (`Fitsᴰ`)

Fits : ∀ {Ψ} → (OVType Ψ → OVType Ψ → Set) → Part Ψ → Set
Fits S (ty _ X Y) = S X Y
Fits S (rg _ _ _) = ⊤
Fits S (eg _ _ _) = ⊤

Fitsᴰ : ∀ {Ψ} {A B : OVType Ψ} → (OVType Ψ → OVType Ψ → Set) → Shape A B → Set
Fitsᴰ S (vars _ _)   = ⊤
Fitsᴰ S (parts ps _) = All (Fits S) ps
Fitsᴰ S clash        = ⊥

Just : ∀ {X : Set} → Maybe X → Set
Just {X} m = Σ[ x ∈ X ] (m ≡ just x)

module SubDecJust {Ψ : Scope} (S : OVType Ψ → OVType Ψ → Set)
                  (S-sym : ∀ {A B} → S A B → S B A)
                  (S-dec : ∀ {A B} → S A B → Fitsᴰ S (decompose A B)) where

  zip₂-Just : ∀ {X Y Z : Set} → (f : X → Y → Z) → {m : Maybe X} {m' : Maybe Y}
            → Just m → Just m' → Just (zip₂ f m m')
  zip₂-Just f (x , refl) (y , refl) = f x y , refl

  atVarᴱ-Just : ∀ {P P' : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → Set} → (v : Variance)
              → {d : Maybe (Exact P)} {e : Maybe (Exact P')} → Just d → Just e
              → Just (atVarᴱ v d e)
  atVarᴱ-Just co     jd je = jd
  atVarᴱ-Just contra jd je = je
  atVarᴱ-Just inv    jd je = zip₂-Just _∧ᴱ_ jd je

  allᴱ-Just : ∀ {X : Set} (R : X → ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → Set) → (xs : List X)
            → {f : ∀ {x} → x ∈ xs → Maybe (Exact (R x))} → (∀ {x} → (m : x ∈ xs) → Just (f m))
            → Just (allᴱ R xs f)
  allᴱ-Just R []       k = _ , refl
  allᴱ-Just R (x ∷ xs) k = zip₂-Just _ (k (here refl)) (allᴱ-Just R xs (λ m → k (there m)))

  subDec-Justᵃ : (A B : OVType Ψ) → (a : Acc _≺_ A) → (b : Acc _≺_ B) → S A B
               → Just (subDecᵃ A B a b)
  partDec-Just : ∀ {A B : OVType Ψ} {ps} → (g : Decomp A B ps)
               → (ra : WfRec _≺_ (Acc _≺_) A) → (rb : WfRec _≺_ (Acc _≺_) B)
               → All (Fits S) ps → ∀ {p} → (m : p ∈ ps) → Just (partDec g ra rb m)

  subDec-Justᵃ A B (acc ra) (acc rb) h with decompose A B | S-dec h
  ... | vars α β   | _  = _ , refl
  ... | parts ps g | fs with allᴱ-Just (λ p Q δ → Holdsᴾ Q (p [ δ ∣ δ ]ᴾ)) ps
                               (partDec-Just g ra rb fs)
  ...   | d , e = fromParts g d , cong (mmap (fromParts g)) e

  partDec-Just g ra rb fs {ty v X Y} m =
    atVarᴱ-Just v (subDec-Justᵃ X Y (ra (left g m)) (rb (right g m)) (lookup fs m))
                  (subDec-Justᵃ Y X (rb (right g m)) (ra (left g m)) (S-sym (lookup fs m)))
  partDec-Just g ra rb fs {rg v ρ ρ'} m = atVarᴱ-Just v (_ , refl) (_ , refl)
  partDec-Just g ra rb fs {eg v ε ε'} m = atVarᴱ-Just v (_ , refl) (_ , refl)

  subDec-Just : ∀ {A B} → S A B → Just (subDec A B)
  subDec-Just {A} {B} = subDec-Justᵃ A B (≺-wf A) (≺-wf B)

nothing≢just : ∀ {X : Set} {x : X} → nothing ≡ just x → ⊥
nothing≢just ()

false≢true : false ≡ true → ⊥
false≢true ()

-- The concatenation of the lists given to the members of a list, if
-- every member is given one

concatᴹ : ∀ {X Y : Set} → (xs : List X) → (∀ {x} → x ∈ xs → Maybe (List Y)) → Maybe (List Y)
concatᴹ []       f = just []
concatᴹ (x ∷ xs) f = zip₂ _++_ (f (here refl)) (concatᴹ xs (λ m → f (there m)))

concatᴹ-⊆ : ∀ {X Y : Set} → (xs : List X) → {f : ∀ {x} → x ∈ xs → Maybe (List Y)}
          → {ys : List Y} → concatᴹ xs f ≡ just ys → ∀ {x} → (m : x ∈ xs)
          → Σ[ zs ∈ List Y ] ((f m ≡ just zs) × (∀ {y} → y ∈ zs → y ∈ ys))
concatᴹ-⊆ (x ∷ xs) {f} e m with zip₂-just _++_ (f (here refl)) (concatᴹ xs (λ m' → f (there m'))) e
concatᴹ-⊆ (x ∷ xs)     e (here refl) | zs , ws , e₁ , e₂ , refl = zs , e₁ , ∈-++⁺ˡ
concatᴹ-⊆ (x ∷ xs) {f} e (there m)   | zs , ws , e₁ , e₂ , refl
  with concatᴹ-⊆ xs {λ m' → f (there m')} e₂ m
... | vs , e₃ , inc = vs , e₃ , (λ n → ∈-++⁺ʳ zs (inc n))

concatᴹ-∈ : ∀ {X Y : Set} → (xs : List X) → {f : ∀ {x} → x ∈ xs → Maybe (List Y)}
          → {ys : List Y} → concatᴹ xs f ≡ just ys → ∀ {y} → y ∈ ys
          → Σ[ x ∈ X ] Σ[ m ∈ x ∈ xs ] Σ[ zs ∈ List Y ] ((f m ≡ just zs) × (y ∈ zs))
concatᴹ-∈ []       refl ()
concatᴹ-∈ (x ∷ xs) {f} e n with zip₂-just _++_ (f (here refl)) (concatᴹ xs (λ m' → f (there m'))) e
... | zs , ws , e₁ , e₂ , refl with ∈-++⁻ zs n
...   | inj₁ n' = x , here refl , zs , e₁ , n'
...   | inj₂ n' with concatᴹ-∈ xs {λ m' → f (there m')} e₂ n'
...     | x' , m , vs , e₃ , n'' = x' , there m , vs , e₃ , n''

concatᴹ-nothing : ∀ {X Y : Set} → (xs : List X) → {f : ∀ {x} → x ∈ xs → Maybe (List Y)}
                → concatᴹ xs f ≡ nothing → Σ[ x ∈ X ] Σ[ m ∈ x ∈ xs ] (f m ≡ nothing)
concatᴹ-nothing (x ∷ xs) {f} e
  with zip₂-nothing _++_ (f (here refl)) (concatᴹ xs (λ m' → f (there m'))) e
... | inj₁ e₁ = x , here refl , e₁
... | inj₂ e₂ with concatᴹ-nothing xs {λ m' → f (there m')} e₂
...   | x' , m , e₃ = x' , there m , e₃

-- An eternality demand reduces along the eternality column to demands
-- on type variables, or is refuted. The recursion is on the parts
-- (`≺-wf`).

etDecᵃ : ∀ {Ψ} → (A : OVType Ψ) → Acc _≺_ A → Maybe (List (TyVar Ψ))
etPart : ∀ {Ψ} {A B : OVType Ψ} {ps} → Decomp A B ps → WfRec _≺_ (Acc _≺_) A
       → ∀ {p} → p ∈ ps → Maybe (List (TyVar Ψ))

etDecᵃ A (acc r) with self A
... | var α       = just (α ∷ [])
... | form ps g _ with eternal g
...   | true  = concatᴹ ps (etPart g r)
...   | false = nothing

etPart g r {ty _ X _} m = etDecᵃ X (r (left g m))
etPart g r {rg _ _ _} m = just []
etPart g r {eg _ _ _} m = just []

etDec : ∀ {Ψ} → OVType Ψ → Maybe (List (TyVar Ψ))
etDec A = etDecᵃ A (≺-wf A)

etDec-introᵃ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (A : OVType Ψ) → (a : Acc _≺_ A)
             → {αs : List (TyVar Ψ)} → etDecᵃ A a ≡ just αs → (δ : Subst Ψ Ψ')
             → (∀ {α} → α ∈ αs → Q ⊩ᴱ tvar α [ δ ]ᵛ) → Q ⊩ᴱ A [ δ ]ᵛ
etDec-introᵃ {Q = Q} A (acc r) e δ k with self A
etDec-introᵃ .(tvar α) (acc r) refl δ k | var α = k (here refl)
... | form ps g _ with eternal g in et
...   | false = ⊥-elim (nothing≢just e)
...   | true  = ⊩ᴱ-intro g et δ (tabulate part)
  where
    part : ∀ {p} → p ∈ ps → Etᴾ Q (p [ δ ∣ δ ]ᴾ)
    part {ty _ X _} m with concatᴹ-⊆ ps e m
    ... | zs , ez , inc = etDec-introᵃ X (r (left g m)) ez δ (λ n → k (inc n))
    part {rg _ _ _} m = tt
    part {eg _ _ _} m = tt

etDec-intro : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (A : OVType Ψ) → {αs : List (TyVar Ψ)}
            → etDec A ≡ just αs → (δ : Subst Ψ Ψ')
            → (∀ {α} → α ∈ αs → Q ⊩ᴱ tvar α [ δ ]ᵛ) → Q ⊩ᴱ A [ δ ]ᵛ
etDec-intro A = etDec-introᵃ A (≺-wf A)

-- The same, read at the identity

etDec-sound : ∀ {Ψ} {Q : Hyps Ψ} → (A : OVType Ψ) → {αs : List (TyVar Ψ)}
            → etDec A ≡ just αs → (∀ {α} → α ∈ αs → Q ⊩ᴱ tvar α) → Q ⊩ᴱ A
etDec-sound {Q = Q} A e k =
  subst (Q ⊩ᴱ_) ([id]ᵛ A)
        (etDec-intro A e idˢ (λ {α} m → subst (Q ⊩ᴱ_) (sym ([id]ᵛ (tvar α))) (k m)))

-- A type that is eternal at some instance mentions no grade, so it
-- strengthens away from any rigid

etDec-str : ∀ {Ψ} → (j : EVar (Ψ +e)) → (A : OVType (Ψ +e)) → {αs : List (TyVar (Ψ +e))}
          → etDec A ≡ just αs → Σ[ A₀ ∈ OVType Ψ ] (strᵛ j A ≡ just A₀)
etDec-str j (tvar α) q = _ , refl
etDec-str j (Base b) q = Base b , refl
etDec-str j Unit     q = Unit , refl
etDec-str j Bool     q = Bool , refl
etDec-str j Empty    q = Empty , refl
etDec-str j (A |×| B) q with zip₂-just _++_ (etDec A) (zip₂ _++_ (etDec B) (just [])) q
... | _ , _ , qa , q' , _ with zip₂-just _++_ (etDec B) (just []) q'
...   | _ , _ , qb , _ , _ with etDec-str j A qa | etDec-str j B qb
...     | A₀ , ra | B₀ , rb = A₀ |×| B₀ , cong₂ (zip₂ _|×|_) ra rb
etDec-str j (A ⇒ (B ‼ ε)) ()
etDec-str j ([ ρ ] A)     ()

-- Conversely, every atom of a successful decomposition is entailed
-- by the demand it came from.

etDec-complᵃ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (A : OVType Ψ) → (a : Acc _≺_ A)
             → {αs : List (TyVar Ψ)} → etDecᵃ A a ≡ just αs → (δ : Subst Ψ Ψ')
             → Q ⊩ᴱ A [ δ ]ᵛ → ∀ {α} → α ∈ αs → Q ⊩ᴱ tvar α [ δ ]ᵛ
etDec-complᵃ {Q = Q} A (acc r) e δ et n with self A
etDec-complᵃ .(tvar α) (acc r) refl δ et (here refl) | var α = et
... | form ps g _ with eternal g
...   | false = ⊥-elim (nothing≢just e)
...   | true with concatᴹ-∈ ps e n
...     | _ , m , zs , ez , n' = part m ez n'
  where
    part : ∀ {p} → (m : p ∈ ps) → ∀ {zs} → etPart g r m ≡ just zs
         → ∀ {α} → α ∈ zs → Q ⊩ᴱ tvar α [ δ ]ᵛ
    part {ty _ X _} m ez n =
      etDec-complᵃ X (r (left g m)) ez δ (lookup (proj₂ (⊩ᴱ-elim g δ et)) m) n
    part {rg _ _ _} m refl ()
    part {eg _ _ _} m refl ()

etDec-compl : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (A : OVType Ψ) → {αs : List (TyVar Ψ)}
            → etDec A ≡ just αs → (δ : Subst Ψ Ψ') → Q ⊩ᴱ A [ δ ]ᵛ
            → ∀ {α} → α ∈ αs → Q ⊩ᴱ tvar α [ δ ]ᵛ
etDec-compl A = etDec-complᵃ A (≺-wf A)

-- A failed decomposition refutes the demand, at every instance:
-- substitution preserves the former, which the column refuses, or a
-- part that is refuted.

etDec-refuteᵃ : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (A : OVType Ψ) → (a : Acc _≺_ A)
              → etDecᵃ A a ≡ nothing → (δ : Subst Ψ Ψ') → ¬ (Q ⊩ᴱ A [ δ ]ᵛ)
etDec-refuteᵃ {Q = Q} A (acc r) e δ et with self A
etDec-refuteᵃ .(tvar α) (acc r) () δ et | var α
... | form ps g _ with eternal g in c
...   | false = false≢true (trans (sym c) (proj₁ (⊩ᴱ-elim g δ et)))
...   | true with concatᴹ-nothing ps e
...     | _ , m , en = part m en
  where
    part : ∀ {p} → (m : p ∈ ps) → etPart g r m ≡ nothing → ⊥
    part {ty _ X _} m en =
      etDec-refuteᵃ X (r (left g m)) en δ (lookup (proj₂ (⊩ᴱ-elim g δ et)) m)
    part {rg _ _ _} m ()
    part {eg _ _ _} m ()
etDec-refute : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (A : OVType Ψ) → etDec A ≡ nothing
             → (δ : Subst Ψ Ψ') → ¬ (Q ⊩ᴱ A [ δ ]ᵛ)
etDec-refute A = etDec-refuteᵃ A (≺-wf A)

-- So a disjunction on such a type is met, from no hypotheses, exactly
-- by its grade side

etDec-grade : ∀ {Ψ Ψ'} → (A : OVType Ψ) → etDec A ≡ nothing → (δ : Subst Ψ Ψ')
            → {ρ : RExp Ψ'} → VarOK ∅ᴴ (A [ δ ]ᵛ) ρ → ∅ᴴ ⊩ ρ ≾̂ᵣ ûᵣ
etDec-grade A e δ (et-ok et)      = ⊥-elim (etDec-refute A e δ et)
etDec-grade A e δ (≾ᵘ-ok le)      = le
etDec-grade A e δ (hyp-ok () _ _)

-- The decomposition of a whole list of eternality demands

record EtsDec {Ψ : Scope} (l : List (OVType Ψ)) : Set where
  constructor etsdec
  field
    varsOf : List (TyVar Ψ)
    introᵗ : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
           → (∀ {α} → α ∈ varsOf → Q ⊩ᴱ tvar α [ δ ]ᵛ)
           → ∀ {A} → A ∈ l → Q ⊩ᴱ A [ δ ]ᵛ
    elimᵗ  : ∀ {Ψ'} {Q : Hyps Ψ'} → (δ : Subst Ψ Ψ')
           → (∀ {A} → A ∈ l → Q ⊩ᴱ A [ δ ]ᵛ)
           → ∀ {α} → α ∈ varsOf → Q ⊩ᴱ tvar α [ δ ]ᵛ

open EtsDec public

-- One demand onto a list, its decomposition paired with the equation
-- naming it

etsCons : ∀ {Ψ} → (A : OVType Ψ) → (l : List (OVType Ψ))
        → (x : Maybe (List (TyVar Ψ))) → etDec A ≡ x → Maybe (EtsDec l)
        → Maybe (EtsDec (A ∷ l))
etsCons A l (just αs) e (just d) =
  just (etsdec (αs ++ varsOf d)
               (λ δ k → λ { (here refl) → etDec-intro A e δ (λ m → k (∈-++⁺ˡ m))
                          ; (there m)   → introᵗ d δ (λ m' → k (∈-++⁺ʳ αs m')) m })
               (λ δ k m → [ etDec-compl A e δ (k (here refl))
                          , elimᵗ d δ (λ m' → k (there m')) ]′ (∈-++⁻ αs m)))
etsCons A l (just _)  e nothing  = nothing
etsCons A l nothing   e _        = nothing

etsDec : ∀ {Ψ} → (l : List (OVType Ψ)) → Maybe (EtsDec l)
etsDec []      = just (etsdec [] (λ δ k ()) (λ δ k ()))
etsDec (A ∷ l) = etsCons A l (etDec A) refl (etsDec l)

-- A failure names an undecomposable demand

etsDec-nothing : ∀ {Ψ} → (l : List (OVType Ψ)) → etsDec l ≡ nothing
               → Σ[ A ∈ OVType Ψ ] ((A ∈ l) × (etDec A ≡ nothing))
etsDec-nothing []      ()
etsDec-nothing {Ψ} (A ∷ l) eq = cons (etDec A) refl (etsDec l) refl eq
  where
    cons : (x : Maybe (List (TyVar Ψ))) → (e : etDec A ≡ x)
         → (y : Maybe (EtsDec l)) → etsDec l ≡ y → etsCons A l x e y ≡ nothing
         → Σ[ B ∈ OVType Ψ ] ((B ∈ A ∷ l) × (etDec B ≡ nothing))
    cons (just _) e (just _) q ()
    cons (just _) e nothing  q _ with etsDec-nothing l q
    ... | B , m , r = B , there m , r
    cons nothing  e _        q _ = A , here refl , e

-- A failure refutes the list at every instance

etsDec-refute : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (l : List (OVType Ψ)) → etsDec l ≡ nothing
              → (δ : Subst Ψ Ψ') → ¬ (∀ {A} → A ∈ l → Q ⊩ᴱ A [ δ ]ᵛ)
etsDec-refute l eq δ k with etsDec-nothing l eq
... | A , m , q = etDec-refute A q δ (k m)

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

-- A residual with its subtyping and eternality demands decomposed: the
-- pairs of type variables stay demands, the grade orderings join the
-- others, the eternality demands are on type variables. It has the
-- instances of the original.

atomiseᴿ : ∀ {Ψ} → (R : Resid Ψ) → SubsDec (ss R) → EtsDec (ts R) → Resid Ψ
atomiseᴿ R d t = resid (rs R ++ aordᵣ (atomsOfˢ d)) (es R ++ aordₑ (atomsOfˢ d))
                       (map tvar (varsOf t)) (map (mapᵖ tvar) (asubᵥ (atomsOfˢ d)))
                       (ds R) (dfs R)

atomiseᴿ-sound : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (R : Resid Ψ)
               → (d : SubsDec (ss R)) → (t : EtsDec (ts R))
               → Q ⊩ᴿ (atomiseᴿ R d t) [ δ ] → Q ⊩ᴿ R [ δ ]
atomiseᴿ-sound {δ = δ} R d t h =
  mk⊩ᴿ (λ m → ⊩rs h (∈-++⁺ˡ m)) (λ m → ⊩es h (∈-++⁺ˡ m))
       (introᵗ t δ (λ m → ⊩ts h (∈-map⁺ tvar m)))
       (introˢ d δ (holds (λ m → ⊩ss h (∈-map⁺ (mapᵖ tvar) m))
                          (λ m → ⊩rs h (∈-++⁺ʳ (rs R) m))
                          (λ m → ⊩es h (∈-++⁺ʳ (es R) m))))
       (⊩ds h) (⊩dfs h)

atomiseᴿ-compl : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {δ : Subst Ψ Ψ'} → (R : Resid Ψ)
               → (d : SubsDec (ss R)) → (t : EtsDec (ts R))
               → Q ⊩ᴿ R [ δ ] → Q ⊩ᴿ (atomiseᴿ R d t) [ δ ]
atomiseᴿ-compl {Q = Q} {δ = δ} R d t h =
  mk⊩ᴿ (λ m → [ ⊩rs h , hr hs ]′ (∈-++⁻ (rs R) m))
       (λ m → [ ⊩es h , he hs ]′ (∈-++⁻ (es R) m))
       ts' (⊩ss (atomsᴿ-⊩ (atomsOfˢ d) hs)) (⊩ds h) (⊩dfs h)
  where
    hs : Holds Q δ (atomsOfˢ d)
    hs = elimˢ d δ (⊩ss h)

    ts' : ∀ {A} → A ∈ map tvar (varsOf t) → Q ⊩ᴱ A [ δ ]ᵛ
    ts' m with ∈-map⁻ tvar m
    ... | α , m₀ , refl = elimᵗ t δ (⊩ts h) m₀

-- The atoms of a residual, its deferred conditions set aside

bareᴿ : ∀ {Ψ} → Resid Ψ → Resid Ψ
bareᴿ R = resid (rs R) (es R) (ts R) (ss R) (ds R) []

⊩ᴿ-bare : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {R : Resid Ψ} {δ : Subst Ψ Ψ'}
        → Q ⊩ᴿ bareᴿ R [ δ ] → (∀ {E} → E ∈ dfs R → Q ⊩ᵈ E [ δ ]) → Q ⊩ᴿ R [ δ ]
⊩ᴿ-bare h f = mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (⊩ss h) (⊩ds h) f

toHyps : ∀ {Ψ} → (R : Resid Ψ) → Maybe (Σ[ Q ∈ Hyps Ψ ] (Q ⊩ᴿ bareᴿ R [ idˢ ]))
toHyps R with etsDec (ts R) | subsList (ss R)
... | nothing | _       = nothing
... | just _  | nothing = nothing
... | just t  | just d  = just (Q , mk⊩ᴿ ordᵣ' ordₑ' ets' subs' disj' (λ ()))
  where
    a : SubAtoms _
    a = atomsOfˢ d

    Q : Hyps _
    Q = hyps (varsOf t) (asubᵥ a) (rs R ++ aordᵣ a) (es R ++ aordₑ a) (ds R)

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
    ets' = introᵗ t idˢ (λ {α} m → subst (Q ⊩ᴱ_) (sym ([id]ᵛ (tvar α))) (et-hyp m))

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
      subst₂ (VarOK Q) (sym ([id]ᵛ A)) (sym ([id]ʳ ρ)) (hyp-ok₀ m)

-- The same, for a whole residual

toHyps-nothing : ∀ {Ψ} → (R : Resid Ψ) → toHyps R ≡ nothing
               → Σ[ A ∈ OVType Ψ ] ((A ∈ ts R) × (etDec A ≡ nothing))
               ⊎ Σ[ A ∈ OVType Ψ ] Σ[ B ∈ OVType Ψ ]
                   (((A , B) ∈ ss R) × (subDec A B ≡ nothing))
toHyps-nothing R eq with etsDec (ts R) in e | subsList (ss R) in e'
... | nothing | _       = inj₁ (etsDec-nothing (ts R) e)
... | just _  | nothing = inj₂ (subsList-nothing (ss R) e')
toHyps-nothing R () | just _ | just _

-- Every atom the read-back raised is entailed by the demands it
-- came from, at every instance

toHyps-compl : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} → (R : Resid Ψ)
             → {p : Σ[ Q₀ ∈ Hyps Ψ ] (Q₀ ⊩ᴿ bareᴿ R [ idˢ ])}
             → toHyps R ≡ just p → (δ : Subst Ψ Ψ')
             → Q ⊩ᴿ R [ δ ] → Q ⊩ᴴ proj₁ p [ δ ]
toHyps-compl R eq δ h with etsDec (ts R) | subsList (ss R)
toHyps-compl R () δ h | nothing | _
toHyps-compl R () δ h | just _  | nothing
toHyps-compl R eq δ h | just t  | just d with eq
... | refl = mk⊩ᴴ (elimᵗ t δ (⊩ts h)) (hv hs) ordᵣ' ordₑ' (⊩ds h)
  where
    hs : Holds _ δ (atomsOfˢ d)
    hs = elimˢ d δ (⊩ss h)

    ordᵣ' : ∀ {ρ ρ'} → (ρ , ρ') ∈ rs R ++ aordᵣ (atomsOfˢ d)
          → _ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
    ordᵣ' m = [ ⊩rs h , hr hs ]′ (∈-++⁻ (rs R) m)

    ordₑ' : ∀ {ε ε'} → (ε , ε') ∈ es R ++ aordₑ (atomsOfˢ d)
          → _ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
    ordₑ' m = [ ⊩es h , he hs ]′ (∈-++⁻ (es R) m)
