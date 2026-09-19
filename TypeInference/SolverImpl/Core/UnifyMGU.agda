------------------------------------------------------------------
-- Most general unifiers, and refutation                        --
--                                                              --
-- A successful run of `unify` returns a store whose denotation --
-- is a most general unifier of the equations: every unifying   --
-- substitution factors through it. A failing run refutes the   --
-- equations, for every substitution that maps the rigid        --
-- variables to variables, injectively.                         --
--                                                              --
-- Both halves are one induction, following the unifier: a call --
-- is specified by what each of its two possible results means  --
-- (`Spec`), so a clash — where nothing needs to be known about --
-- the result — is discharged by refuting its equation alone,   --
-- with no case analysis on the size index.                     --
--                                                              --
-- The properties spoken about are properties of substitutions  --
-- closed under `_≐ˢ_`, composed with a substitution by `_⋄_`;  --
-- `Max` is maximality relative to the store a call starts      --
-- from, and `seq-spec` is the optimist's lemma: maximal        --
-- solutions of two properties in sequence compose.             --
--                                                              --
-- Failure has three sources. A clash is a head mismatch, and   --
-- is immediate because satisfaction is syntactic equality. A   --
-- failed occurrence check is refuted by the cross-sort sizes:  --
-- a proper occurrence of a variable makes the instance of the  --
-- expression strictly larger than the instance of the          --
-- variable. A rigid variable refuses to be bound, which is     --
-- refuted by its image being a variable, distinct from the     --
-- image of every other rigid variable.                         --
--                                                              --
-- The `Max` characterisation of most general unifiers and the  --
-- optimist's lemma follow McBride (JFP 2003).                  --
------------------------------------------------------------------

open import Data.Bool.Base using (if_then_else_; _∨_; true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; punchIn)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; mapMaybe)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′; _>>=_; _<∣>_)
  renaming (map to mmap)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; m≤n+m; m≤n⇒m≤1+n; 1+n≰n)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Core.UnifyMGU (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (BaseType; _≡ᵇ?_)

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S

open import TypeInference.SolverImpl.Core.Thick
open import TypeInference.SolverImpl.Core.For       S
open import TypeInference.SolverImpl.Core.AList     S
open import TypeInference.SolverImpl.Core.Eqn       S
open import TypeInference.SolverImpl.Core.Occurs    S
open import TypeInference.SolverImpl.Core.Size      S
open import TypeInference.SolverImpl.Core.Unify     S
open import TypeInference.SolverImpl.Core.UnifySound S

--------------------------------------------------------------
-- The algebra of pointwise equality of substitutions        --
--------------------------------------------------------------

refl≐ˢ : ∀ {Θ Θ'} {σ : Subst Θ Θ'} → σ ≐ˢ σ
refl≐ˢ = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

trans≐ˢ : ∀ {Θ Θ'} {σ δ γ : Subst Θ Θ'} → σ ≐ˢ δ → δ ≐ˢ γ → σ ≐ˢ γ
trans≐ˢ q r = mk≐ˢ (λ α → trans (≐ᵗ q α) (≐ᵗ r α))
                   (λ i → trans (≐ʳ q i) (≐ʳ r i))
                   (λ i → trans (≐ᵉ q i) (≐ᵉ r i))

⨟ˢ-assoc : ∀ {Θ₁ Θ₂ Θ₃ Θ₄} → (σ : Subst Θ₁ Θ₂) → (δ : Subst Θ₂ Θ₃) → (γ : Subst Θ₃ Θ₄)
         → ((σ ⨟ˢ δ) ⨟ˢ γ) ≐ˢ (σ ⨟ˢ (δ ⨟ˢ γ))
⨟ˢ-assoc σ δ γ = mk≐ˢ (λ α → [⨟]ᵛ (sTy σ α) δ γ)
                      (λ i → [⨟]ʳ (sR σ i) δ γ)
                      (λ i → [⨟]ᵉ (sE σ i) δ γ)

⨟ˢ-congʳ : ∀ {Θ₁ Θ₂ Θ₃} → (σ : Subst Θ₁ Θ₂) → {δ γ : Subst Θ₂ Θ₃} → δ ≐ˢ γ
         → (σ ⨟ˢ δ) ≐ˢ (σ ⨟ˢ γ)
⨟ˢ-congʳ σ q = mk≐ˢ (λ α → [≐]ᵛ q (sTy σ α))
                    (λ i → [≐]ʳ q (sR σ i))
                    (λ i → [≐]ᵉ q (sE σ i))

--------------------------------------------------------------
-- Further inversions of the combinators of the unifier      --
--------------------------------------------------------------

bind-nothing : ∀ {X Y : Set} → (m : Maybe X) → (f : X → Maybe Y) → (m >>= f) ≡ nothing
             → (m ≡ nothing) ⊎ Σ[ x ∈ X ] ((m ≡ just x) × (f x ≡ nothing))
bind-nothing nothing  f q = inj₁ refl
bind-nothing (just x) f q = inj₂ (x , refl , q)

alt-nothing : ∀ {X : Set} → (m m' : Maybe X) → (m <∣> m') ≡ nothing
            → (m ≡ nothing) × (m' ≡ nothing)
alt-nothing nothing  m' q = refl , q
alt-nothing (just x) m' ()

map-nothing : ∀ {X Y : Set} → (f : X → Y) → (m : Maybe X) → mmap f m ≡ nothing → m ≡ nothing
map-nothing f nothing  q = refl
map-nothing f (just x) ()

if-nothing : ∀ {X : Set} → (b : 𝔹) → (x : X) → (if b then nothing else just x) ≡ nothing
           → b ≡ true
if-nothing true  x q = refl
if-nothing false x ()

if-no : ∀ {X : Set} → (b : 𝔹) → (m : Maybe X) → (if b then nothing else m) ≡ nothing
      → (b ≡ true) ⊎ (m ≡ nothing)
if-no true  m q = inj₁ refl
if-no false m q = inj₂ q

dec-if-nothing : ∀ {P X : Set} → (d : Dec P) → (m m' : Maybe X)
               → (if ⌊ d ⌋ then m else m') ≡ nothing
               → (P × (m ≡ nothing)) ⊎ ((¬ P) × (m' ≡ nothing))
dec-if-nothing (yes r) m m' q = inj₁ (r , q)
dec-if-nothing (no nr) m m' q = inj₂ (nr , q)

dec-true : ∀ {P : Set} → (d : Dec P) → P → ⌊ d ⌋ ≡ true
dec-true (yes _) _ = refl
dec-true (no nr) r = ⊥-elim (nr r)

true-dec : ∀ {P : Set} → (d : Dec P) → ⌊ d ⌋ ≡ true → P
true-dec (yes r) q = r
true-dec (no  _) ()

dec-no : ∀ {P : Set} → (d : Dec P) → ¬ P → ⌊ d ⌋ ≡ false
dec-no (yes r) nr = ⊥-elim (nr r)
dec-no (no  _) _  = refl

∨-true : (b b' : 𝔹) → (b ∨ b') ≡ true → (b ≡ true) ⊎ (b' ≡ true)
∨-true true  b' q = inj₁ refl
∨-true false b' q = inj₂ q

∨-right : (b b' : 𝔹) → b' ≡ true → (b ∨ b') ≡ true
∨-right true  b' q = refl
∨-right false b' q = q

∨-left : (b b' : 𝔹) → b ≡ true → (b ∨ b') ≡ true
∨-left true  b' q = refl
∨-left false b' ()

just-inj : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
just-inj refl = refl

--------------------------------------------------------------
-- The formers are injective                                 --
--------------------------------------------------------------

tvar-inj : ∀ {Θ} {α β : TyVar Θ} → tvar {Θ} α ≡ tvar β → α ≡ β
tvar-inj refl = refl

Base-inj : ∀ {Θ} {b b' : BaseType} → Base {Θ} b ≡ Base b' → b ≡ b'
Base-inj refl = refl

×-inj : ∀ {Θ} {A A' B B' : OVType Θ} → (A |×| A') ≡ (B |×| B') → (A ≡ B) × (A' ≡ B')
×-inj refl = refl , refl

⇒-inj : ∀ {Θ} {A B : OVType Θ} {C D : OCType Θ} → (A ⇒ C) ≡ (B ⇒ D) → (A ≡ B) × (C ≡ D)
⇒-inj refl = refl , refl

box-inj : ∀ {Θ} {ρ ρ' : RExp Θ} {A B : OVType Θ} → ([ ρ ] A) ≡ ([ ρ' ] B) → (ρ ≡ ρ') × (A ≡ B)
box-inj refl = refl , refl

‼-inj : ∀ {Θ} {A B : OVType Θ} {ε ε' : EExp Θ} → (A ‼ ε) ≡ (B ‼ ε') → (A ≡ B) × (ε ≡ ε')
‼-inj refl = refl , refl

rconst-inj : ∀ {Θ} {c d : R} → rconst {Θ} c ≡ rconst d → c ≡ d
rconst-inj refl = refl

·ᵣ-inj : ∀ {Θ} {ρ₁ ρ₂ ρ₁' ρ₂' : RExp Θ} → (ρ₁ ·̂ᵣ ρ₂) ≡ (ρ₁' ·̂ᵣ ρ₂') → (ρ₁ ≡ ρ₁') × (ρ₂ ≡ ρ₂')
·ᵣ-inj refl = refl , refl

∣∣-inj : ∀ {Θ} {ε ε' : EExp Θ} → ∣ ε ∣̂ᵉ ≡ ∣ ε' ∣̂ᵉ → ε ≡ ε'
∣∣-inj refl = refl

evar-inj : ∀ {Θ} {i j : EVar Θ} → evar {Θ} i ≡ evar j → i ≡ j
evar-inj refl = refl

econst-inj : ∀ {Θ} {c d : E} → econst {Θ} c ≡ econst d → c ≡ d
econst-inj refl = refl

·ₑ-inj : ∀ {Θ} {ε₁ ε₂ ε₁' ε₂' : EExp Θ} → (ε₁ ·̂ₑ ε₂) ≡ (ε₁' ·̂ₑ ε₂') → (ε₁ ≡ ε₁') × (ε₂ ≡ ε₂')
·ₑ-inj refl = refl , refl

--------------------------------------------------------------
-- Substitutions that fix the rigid variables                --
--                                                           --
-- A rigid variable goes to a variable, and two distinct      --
-- rigids go to distinct variables.                           --
--------------------------------------------------------------

record Fixing {Θ Ψ : Scope} (rg : Rig Θ) (σ : Subst Θ Ψ) : Set where
  constructor fixing
  field
    fixᵉ : (i : EVar Θ) → i ∈ᶠ rg ≡ true → Σ[ j ∈ EVar Ψ ] (sE σ i ≡ evar j)
    injᵉ : (i i' : EVar Θ) → i ∈ᶠ rg ≡ true → i' ∈ᶠ rg ≡ true → sE σ i ≡ sE σ i' → i ≡ i'

open Fixing public

Fixing-resp : ∀ {Θ Ψ} {rg : Rig Θ} {σ δ : Subst Θ Ψ} → σ ≐ˢ δ → Fixing rg σ → Fixing rg δ
Fixing-resp q (fixing v n) =
  fixing (λ i m → proj₁ (v i m) , trans (sym (≐ᵉ q i)) (proj₂ (v i m)))
         (λ i i' m m' r → n i i' m m' (trans (≐ᵉ q i) (trans r (sym (≐ᵉ q i')))))

-- The identity fixes every rigid list

Fixing-id : ∀ {Θ} → (rg : Rig Θ) → Fixing rg (idˢ {Θ})
Fixing-id rg = fixing (λ i _ → i , refl) (λ i i' _ _ r → evar-inj r)

-- A member of a thickened rigid list comes from a member

∈-mapMaybe : ∀ {Θ} → (i : EVar (Θ +e)) → (rg : Rig (Θ +e)) → (j : EVar Θ)
           → j ∈ᶠ mapMaybe (thickᵉ {Θ} i) rg ≡ true
           → Σ[ i' ∈ EVar (Θ +e) ] ((i' ∈ᶠ rg ≡ true) × (thickᵉ {Θ} i i' ≡ just j))
∈-mapMaybe i [] j ()
∈-mapMaybe {Θ} i (i₀ ∷ rg) j q with thickᵉ {Θ} i i₀ in r
... | nothing with ∈-mapMaybe {Θ} i rg j q
...   | i' , m , r' = i' , ∨-right ⌊ i' ≟ᶠ i₀ ⌋ (i' ∈ᶠ rg) m , r'
∈-mapMaybe {Θ} i (i₀ ∷ rg) j q
    | just j₀ with ∨-true ⌊ j ≟ᶠ j₀ ⌋ (j ∈ᶠ mapMaybe (thickᵉ {Θ} i) rg) q
... | inj₁ s = i₀ , ∨-left ⌊ i₀ ≟ᶠ i₀ ⌋ (i₀ ∈ᶠ rg) (dec-true (i₀ ≟ᶠ i₀) refl) ,
                   trans r (cong just (sym (true-dec (j ≟ᶠ j₀) s)))
... | inj₂ s with ∈-mapMaybe {Θ} i rg j s
...   | i' , m , r' = i' , ∨-right ⌊ i' ≟ᶠ i₀ ⌋ (i' ∈ᶠ rg) m , r'

--------------------------------------------------------------
-- Properties of substitutions                               --
--------------------------------------------------------------

record Property (Θ : Scope) : Set₁ where
  constructor prop
  field
    at   : ∀ {Ψ} → Subst Θ Ψ → Set
    resp≐ : ∀ {Ψ} {σ δ : Subst Θ Ψ} → σ ≐ˢ δ → at σ → at δ

open Property public

-- Composing a property with a substitution

infixl 30 _⋄_

_⋄_ : ∀ {Θ Θ'} → Property Θ → Subst Θ Θ' → Property Θ'
P ⋄ τ = prop (λ δ → at P (τ ⨟ˢ δ)) (λ q u → resp≐ P (⨟ˢ-congʳ τ q) u)

-- The two properties the unifier is asked about

Uni : ∀ {Θ} → Eqn Θ → Property Θ
Uni e = prop (λ σ → Unifies¹ e σ) (λ q u → Unifies¹-resp-≐ˢ q e u)

Unis : ∀ {Θ} → Eqns Θ → Property Θ
Unis es = prop (λ σ → Unifies es σ) (λ q u → Unifies-resp-≐ˢ q es u)

--------------------------------------------------------------
-- What one call of the unifier establishes                  --
--                                                           --
-- Maximality is relative to the store the call starts from:  --
-- every solution of the property extending that store is an  --
-- instance of the returned store.                            --
--------------------------------------------------------------

record Max {Θ Θ' Θ'' : Scope} (P : Property Θ) (ρ : AList Θ Θ') (ρ'' : AList Θ Θ'') : Set where
  constructor max
  field
    fact : ∀ {Ψ} → (δ : Subst Θ' Ψ) → at (P ⋄ ⟦ ρ ⟧ᴬ) δ
         → Σ[ δ' ∈ Subst Θ'' Ψ ] ((⟦ ρ'' ⟧ᴬ ⨟ˢ δ') ≐ˢ (⟦ ρ ⟧ᴬ ⨟ˢ δ))

open Max public

record Spec {Θ Θ' : Scope} (rg : Rig Θ) (P : Property Θ) (ρ : AList Θ Θ')
            (m : Maybe (Sol Θ)) : Set where
  constructor spec
  field
    onJust    : ∀ {Θ''} {ρ'' : AList Θ Θ''} → m ≡ just (Θ'' , ρ'') → Max P ρ ρ''
    onNothing : m ≡ nothing → ∀ {Ψ} → (δ : Subst Θ' Ψ) → Fixing rg (⟦ ρ ⟧ᴬ ⨟ˢ δ)
              → ¬ at (P ⋄ ⟦ ρ ⟧ᴬ) δ

open Spec public

--------------------------------------------------------------
-- The shapes of verdict                                     --
--------------------------------------------------------------

Max-id : ∀ {Θ Θ'} {P : Property Θ} {ρ : AList Θ Θ'} → Max P ρ ρ
Max-id = max (λ δ u → δ , refl≐ˢ)

-- The store is returned unchanged

keep : ∀ {Θ Θ'} {rg : Rig Θ} {P : Property Θ} {ρ : AList Θ Θ'} → Spec rg P ρ (just (Θ' , ρ))
keep = spec (λ { refl → Max-id }) (λ ())

-- The property has no solution at all: the verdict is immaterial

clash : ∀ {Θ Θ'} {rg : Rig Θ} {P : Property Θ} {ρ : AList Θ Θ'} {m : Maybe (Sol Θ)}
      → (∀ {Ψ} → (δ : Subst Θ' Ψ) → ¬ at (P ⋄ ⟦ ρ ⟧ᴬ) δ) → Spec rg P ρ m
clash nc = spec (λ _ → max (λ δ u → ⊥-elim (nc δ u))) (λ _ δ _ → nc δ)

-- The verdict is nothing, and the property has no rigid-fixing solution

refute : ∀ {Θ Θ'} {rg : Rig Θ} {P : Property Θ} {ρ : AList Θ Θ'}
       → (∀ {Ψ} → (δ : Subst Θ' Ψ) → Fixing rg (⟦ ρ ⟧ᴬ ⨟ˢ δ) → ¬ at (P ⋄ ⟦ ρ ⟧ᴬ) δ)
       → Spec rg P ρ nothing
refute nc = spec (λ ()) (λ _ → nc)

-- Comparing two constants

const-spec : ∀ {Θ Θ'} {rg : Rig Θ} {P : Property Θ} {ρ : AList Θ Θ'} {Q : Set}
           → (d : Dec Q) → (∀ {Ψ} → (δ : Subst Θ' Ψ) → at (P ⋄ ⟦ ρ ⟧ᴬ) δ → Q)
           → Spec rg P ρ (if ⌊ d ⌋ then just (Θ' , ρ) else nothing)
const-spec (yes r) f = keep
const-spec (no nr) f = clash (λ δ u → nr (f δ u))

-- Weakening the property along an implication

Max-map : ∀ {Θ Θ' Θ''} {P P' : Property Θ} {ρ : AList Θ Θ'} {ρ'' : AList Θ Θ''}
        → (∀ {Ψ} {σ : Subst Θ Ψ} → at P' σ → at P σ) → Max P ρ ρ'' → Max P' ρ ρ''
Max-map f (max g) = max (λ δ u → g δ (f u))

Spec-map : ∀ {Θ Θ'} {rg : Rig Θ} {P P' : Property Θ} {ρ : AList Θ Θ'} {m : Maybe (Sol Θ)}
         → (∀ {Ψ} {σ : Subst Θ Ψ} → at P' σ → at P σ) → Spec rg P ρ m → Spec rg P' ρ m
Spec-map f (spec j n) = spec (λ q → Max-map f (j q)) (λ q δ fx u → n q δ fx (f u))

-- Substituting into an equation before solving it

Unifies¹-[]ᴱ⁻ : ∀ {Θ Θ' Θ''} → (e : Eqn Θ) → (τ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
              → Unifies¹ e (τ ⨟ˢ δ) → Unifies¹ (e [ τ ]ᴱ) δ
Unifies¹-[]ᴱ⁻ (eqᵛ A B)  τ δ u = trans ([⨟]ᵛ A τ δ) (trans u (sym ([⨟]ᵛ B τ δ)))
Unifies¹-[]ᴱ⁻ (eqᶜ C D)  τ δ u = trans ([⨟]ᶜ C τ δ) (trans u (sym ([⨟]ᶜ D τ δ)))
Unifies¹-[]ᴱ⁻ (eqʳ ρ ρ') τ δ u = trans ([⨟]ʳ ρ τ δ) (trans u (sym ([⨟]ʳ ρ' τ δ)))
Unifies¹-[]ᴱ⁻ (eqᵉ ε ε') τ δ u = trans ([⨟]ᵉ ε τ δ) (trans u (sym ([⨟]ᵉ ε' τ δ)))

--------------------------------------------------------------
-- The optimist's lemma                                      --
--                                                           --
-- Two calls in sequence: the second one starts from the      --
-- store the first one returned, and the factorisations       --
-- compose.                                                   --
--------------------------------------------------------------

seq-spec : ∀ {Θ Θ'} {rg : Rig Θ} {P P₁ P₂ : Property Θ} {ρ : AList Θ Θ'}
         → (m : Maybe (Sol Θ)) → (f : Sol Θ → Maybe (Sol Θ))
         → Spec rg P₁ ρ m
         → (∀ {Θ₁} → (ρ₁ : AList Θ Θ₁) → Spec rg P₂ ρ₁ (f (Θ₁ , ρ₁)))
         → (∀ {Ψ} {σ : Subst Θ Ψ} → at P σ → at P₁ σ × at P₂ σ)
         → Spec rg P ρ (m >>= f)
seq-spec {Θ} {Θ'} {rg} {P} {P₁} {P₂} {ρ} m f s₁ s₂ split = spec yes' no'
  where
    yes' : ∀ {Θ₂} {ρ₂ : AList Θ Θ₂} → (m >>= f) ≡ just (Θ₂ , ρ₂) → Max P ρ ρ₂
    yes' q with bind-just m f q
    ... | (Θ₁ , ρ₁) , q₁ , q₂ = max (λ δ u →
            let r₁ = fact (onJust s₁ q₁) δ (proj₁ (split u))
                r₂ = fact (onJust (s₂ ρ₁) q₂) (proj₁ r₁)
                          (resp≐ P₂ (sym≐ˢ (proj₂ r₁)) (proj₂ (split u)))
            in proj₁ r₂ , trans≐ˢ (proj₂ r₂) (proj₂ r₁))

    no' : (m >>= f) ≡ nothing → ∀ {Ψ} → (δ : Subst Θ' Ψ) → Fixing rg (⟦ ρ ⟧ᴬ ⨟ˢ δ)
        → ¬ at (P ⋄ ⟦ ρ ⟧ᴬ) δ
    no' q δ fx u with bind-nothing m f q
    ... | inj₁ r = onNothing s₁ r δ fx (proj₁ (split u))
    ... | inj₂ ((Θ₁ , ρ₁) , r₁ , r₂) =
            let h = proj₂ (fact (onJust s₁ r₁) δ (proj₁ (split u)))
            in onNothing (s₂ ρ₁) r₂ _ (Fixing-resp (sym≐ˢ h) fx)
                         (resp≐ P₂ (sym≐ˢ h) (proj₂ (split u)))

--------------------------------------------------------------
-- The two alternatives of a flexible-flexible verdict       --
--------------------------------------------------------------

alt-spec : ∀ {Θ Θ'} {rg : Rig Θ} {P : Property Θ} {ρ : AList Θ Θ'}
         → (m m' : Maybe (Sol Θ))
         → (∀ {Θ₂} {ρ₂ : AList Θ Θ₂} → m ≡ just (Θ₂ , ρ₂) → Max P ρ ρ₂)
         → (∀ {Θ₂} {ρ₂ : AList Θ Θ₂} → m' ≡ just (Θ₂ , ρ₂) → Max P ρ ρ₂)
         → (m ≡ nothing → m' ≡ nothing → ∀ {Ψ} → (δ : Subst Θ' Ψ)
              → Fixing rg (⟦ ρ ⟧ᴬ ⨟ˢ δ) → ¬ at (P ⋄ ⟦ ρ ⟧ᴬ) δ)
         → Spec rg P ρ (m <∣> m')
alt-spec {Θ} {Θ'} {rg} {P} {ρ} m m' j₁ j₂ n = spec yes' no'
  where
    yes' : ∀ {Θ₂} {ρ₂ : AList Θ Θ₂} → (m <∣> m') ≡ just (Θ₂ , ρ₂) → Max P ρ ρ₂
    yes' q with alt-just m m' q
    ... | inj₁ r = j₁ r
    ... | inj₂ r = j₂ r

    no' : (m <∣> m') ≡ nothing → ∀ {Ψ} → (δ : Subst Θ' Ψ) → Fixing rg (⟦ ρ ⟧ᴬ ⨟ˢ δ)
        → ¬ at (P ⋄ ⟦ ρ ⟧ᴬ) δ
    no' q with alt-nothing m m' q
    ... | r , r' = n r r'

--------------------------------------------------------------
-- Descending through one binding of the store               --
--------------------------------------------------------------

glueᵗ : ∀ {Θ Θ' Θ'' Ψ} → (X : OVType Θ) → (α : TyVar (Θ +ty))
      → (τ : AList Θ Θ') → (τ' : AList Θ Θ'')
      → (δ : Subst Θ' Ψ) → (δ' : Subst Θ'' Ψ) → (⟦ τ' ⟧ᴬ ⨟ˢ δ') ≐ˢ (⟦ τ ⟧ᴬ ⨟ˢ δ)
      → (⟦ X /ᵗ α ∷ τ' ⟧ᴬ ⨟ˢ δ') ≐ˢ (⟦ X /ᵗ α ∷ τ ⟧ᴬ ⨟ˢ δ)
glueᵗ X α τ τ' δ δ' h =
  trans≐ˢ (⨟ˢ-assoc (X forᵗ α) ⟦ τ' ⟧ᴬ δ')
          (trans≐ˢ (⨟ˢ-congʳ (X forᵗ α) h) (sym≐ˢ (⨟ˢ-assoc (X forᵗ α) ⟦ τ ⟧ᴬ δ)))

glueʳ : ∀ {Θ Θ' Θ'' Ψ} → (X : RExp Θ) → (i : RVar (Θ +r))
      → (τ : AList Θ Θ') → (τ' : AList Θ Θ'')
      → (δ : Subst Θ' Ψ) → (δ' : Subst Θ'' Ψ) → (⟦ τ' ⟧ᴬ ⨟ˢ δ') ≐ˢ (⟦ τ ⟧ᴬ ⨟ˢ δ)
      → (⟦ X /ʳ i ∷ τ' ⟧ᴬ ⨟ˢ δ') ≐ˢ (⟦ X /ʳ i ∷ τ ⟧ᴬ ⨟ˢ δ)
glueʳ X i τ τ' δ δ' h =
  trans≐ˢ (⨟ˢ-assoc (X forʳ i) ⟦ τ' ⟧ᴬ δ')
          (trans≐ˢ (⨟ˢ-congʳ (X forʳ i) h) (sym≐ˢ (⨟ˢ-assoc (X forʳ i) ⟦ τ ⟧ᴬ δ)))

glueᵉ : ∀ {Θ Θ' Θ'' Ψ} → (X : EExp Θ) → (i : EVar (Θ +e))
      → (τ : AList Θ Θ') → (τ' : AList Θ Θ'')
      → (δ : Subst Θ' Ψ) → (δ' : Subst Θ'' Ψ) → (⟦ τ' ⟧ᴬ ⨟ˢ δ') ≐ˢ (⟦ τ ⟧ᴬ ⨟ˢ δ)
      → (⟦ X /ᵉ i ∷ τ' ⟧ᴬ ⨟ˢ δ') ≐ˢ (⟦ X /ᵉ i ∷ τ ⟧ᴬ ⨟ˢ δ)
glueᵉ X i τ τ' δ δ' h =
  trans≐ˢ (⨟ˢ-assoc (X forᵉ i) ⟦ τ' ⟧ᴬ δ')
          (trans≐ˢ (⨟ˢ-congʳ (X forᵉ i) h) (sym≐ˢ (⨟ˢ-assoc (X forᵉ i) ⟦ τ ⟧ᴬ δ)))

-- Rigidity passes through a binding: the two sorts that leave the
-- effect-grade counter alone transport it verbatim, and eliminating
-- an effect-grade variable renumbers the rigids downwards.

Fixing-∷ᵗ : ∀ {Θ Θ' Ψ} → (X : OVType Θ) → (α : TyVar (Θ +ty)) → {rg : Rig (Θ +ty)}
          → (τ : AList Θ Θ') → (δ : Subst Θ' Ψ)
          → Fixing rg (⟦ X /ᵗ α ∷ τ ⟧ᴬ ⨟ˢ δ) → Fixing rg (⟦ τ ⟧ᴬ ⨟ˢ δ)
Fixing-∷ᵗ X α τ δ (fixing v n) = fixing (λ i m → v i m) (λ i i' m m' r → n i i' m m' r)

Fixing-∷ʳ : ∀ {Θ Θ' Ψ} → (X : RExp Θ) → (i : RVar (Θ +r)) → {rg : Rig (Θ +r)}
          → (τ : AList Θ Θ') → (δ : Subst Θ' Ψ)
          → Fixing rg (⟦ X /ʳ i ∷ τ ⟧ᴬ ⨟ˢ δ) → Fixing rg (⟦ τ ⟧ᴬ ⨟ˢ δ)
Fixing-∷ʳ X i τ δ (fixing v n) = fixing (λ j m → v j m) (λ j j' m m' r → n j j' m m' r)

Fixing-∷ᵉ : ∀ {Θ Θ' Ψ} → (X : EExp Θ) → (i : EVar (Θ +e)) → {rg : Rig (Θ +e)}
          → (τ : AList Θ Θ') → (δ : Subst Θ' Ψ)
          → Fixing rg (⟦ X /ᵉ i ∷ τ ⟧ᴬ ⨟ˢ δ) → Fixing (popʳᵍ τ i rg) (⟦ τ ⟧ᴬ ⨟ˢ δ)
Fixing-∷ᵉ {Θ} {Θ'} {Ψ} X i {rg} τ δ fx = fixing v' n'
  where
    step : (j : EVar (Θ +e)) → (j' : EVar Θ) → thickᵉ {Θ} i j ≡ just j'
         → sE (⟦ X /ᵉ i ∷ τ ⟧ᴬ ⨟ˢ δ) j ≡ sE (⟦ τ ⟧ᴬ ⨟ˢ δ) j'
    step j j' r = cong (λ z → (maybe′ evar X z [ ⟦ τ ⟧ᴬ ]ᵉ) [ δ ]ᵉ) r

    v' : (j : EVar Θ) → j ∈ᶠ popʳᵍ τ i rg ≡ true
       → Σ[ k ∈ EVar Ψ ] (sE (⟦ τ ⟧ᴬ ⨟ˢ δ) j ≡ evar k)
    v' j m with ∈-mapMaybe {Θ} i rg j m
    ... | j₀ , m₀ , r with fixᵉ fx j₀ m₀
    ...   | k , s = k , trans (sym (step j₀ j r)) s

    n' : (j j' : EVar Θ) → j ∈ᶠ popʳᵍ τ i rg ≡ true → j' ∈ᶠ popʳᵍ τ i rg ≡ true
       → sE (⟦ τ ⟧ᴬ ⨟ˢ δ) j ≡ sE (⟦ τ ⟧ᴬ ⨟ˢ δ) j' → j ≡ j'
    n' j j' m m' u with ∈-mapMaybe {Θ} i rg j m | ∈-mapMaybe {Θ} i rg j' m'
    ... | j₀ , m₀ , r | j₀' , m₀' , r' =
          just-inj (trans (sym r)
                   (trans (cong (thickᵉ {Θ} i)
                                (injᵉ fx j₀ j₀' m₀ m₀'
                                      (trans (step j₀ j r) (trans u (sym (step j₀' j' r'))))))
                          r'))

descᵗ-spec : ∀ {Θ Θ'} → (X : OVType Θ) → (α : TyVar (Θ +ty)) → (rg : Rig (Θ +ty))
           → (e : Eqn (Θ +ty)) → (τ : AList Θ Θ') → {m : Maybe (Sol Θ)}
           → Spec rg (Uni (e [ X forᵗ α ]ᴱ)) τ m
           → Spec rg (Uni e) (X /ᵗ α ∷ τ) (mmap (consᵗ X α) m)
descᵗ-spec {Θ} {Θ'} X α rg e τ {m} s = spec yes' no'
  where
    down : ∀ {Ψ} → (δ : Subst Θ' Ψ) → Unifies¹ e (⟦ X /ᵗ α ∷ τ ⟧ᴬ ⨟ˢ δ)
         → Unifies¹ (e [ X forᵗ α ]ᴱ) (⟦ τ ⟧ᴬ ⨟ˢ δ)
    down δ u = Unifies¹-[]ᴱ⁻ e (X forᵗ α) (⟦ τ ⟧ᴬ ⨟ˢ δ)
                 (Unifies¹-resp-≐ˢ (⨟ˢ-assoc (X forᵗ α) ⟦ τ ⟧ᴬ δ) e u)

    yes' : ∀ {Θ''} {ρ'' : AList (Θ +ty) Θ''} → mmap (consᵗ X α) m ≡ just (Θ'' , ρ'')
         → Max (Uni e) (X /ᵗ α ∷ τ) ρ''
    yes' q with map-just (consᵗ X α) m q
    ... | (Θ₂ , τ') , q' , refl = max (λ δ u →
            let r = fact (onJust s q') δ (down δ u)
            in proj₁ r , glueᵗ X α τ τ' δ (proj₁ r) (proj₂ r))

    no' : mmap (consᵗ X α) m ≡ nothing → ∀ {Ψ} → (δ : Subst Θ' Ψ)
        → Fixing rg (⟦ X /ᵗ α ∷ τ ⟧ᴬ ⨟ˢ δ) → ¬ Unifies¹ e (⟦ X /ᵗ α ∷ τ ⟧ᴬ ⨟ˢ δ)
    no' q δ fx u = onNothing s (map-nothing (consᵗ X α) m q) δ (Fixing-∷ᵗ X α τ δ fx) (down δ u)

descʳ-spec : ∀ {Θ Θ'} → (X : RExp Θ) → (i : RVar (Θ +r)) → (rg : Rig (Θ +r))
           → (e : Eqn (Θ +r)) → (τ : AList Θ Θ') → {m : Maybe (Sol Θ)}
           → Spec rg (Uni (e [ X forʳ i ]ᴱ)) τ m
           → Spec rg (Uni e) (X /ʳ i ∷ τ) (mmap (consʳ X i) m)
descʳ-spec {Θ} {Θ'} X i rg e τ {m} s = spec yes' no'
  where
    down : ∀ {Ψ} → (δ : Subst Θ' Ψ) → Unifies¹ e (⟦ X /ʳ i ∷ τ ⟧ᴬ ⨟ˢ δ)
         → Unifies¹ (e [ X forʳ i ]ᴱ) (⟦ τ ⟧ᴬ ⨟ˢ δ)
    down δ u = Unifies¹-[]ᴱ⁻ e (X forʳ i) (⟦ τ ⟧ᴬ ⨟ˢ δ)
                 (Unifies¹-resp-≐ˢ (⨟ˢ-assoc (X forʳ i) ⟦ τ ⟧ᴬ δ) e u)

    yes' : ∀ {Θ''} {ρ'' : AList (Θ +r) Θ''} → mmap (consʳ X i) m ≡ just (Θ'' , ρ'')
         → Max (Uni e) (X /ʳ i ∷ τ) ρ''
    yes' q with map-just (consʳ X i) m q
    ... | (Θ₂ , τ') , q' , refl = max (λ δ u →
            let r = fact (onJust s q') δ (down δ u)
            in proj₁ r , glueʳ X i τ τ' δ (proj₁ r) (proj₂ r))

    no' : mmap (consʳ X i) m ≡ nothing → ∀ {Ψ} → (δ : Subst Θ' Ψ)
        → Fixing rg (⟦ X /ʳ i ∷ τ ⟧ᴬ ⨟ˢ δ) → ¬ Unifies¹ e (⟦ X /ʳ i ∷ τ ⟧ᴬ ⨟ˢ δ)
    no' q δ fx u = onNothing s (map-nothing (consʳ X i) m q) δ (Fixing-∷ʳ X i τ δ fx) (down δ u)

descᵉ-spec : ∀ {Θ Θ'} → (X : EExp Θ) → (i : EVar (Θ +e)) → (rg : Rig (Θ +e))
           → (e : Eqn (Θ +e)) → (τ : AList Θ Θ') → {m : Maybe (Sol Θ)}
           → Spec (popʳᵍ τ i rg) (Uni (e [ X forᵉ i ]ᴱ)) τ m
           → Spec rg (Uni e) (X /ᵉ i ∷ τ) (mmap (consᵉ X i) m)
descᵉ-spec {Θ} {Θ'} X i rg e τ {m} s = spec yes' no'
  where
    down : ∀ {Ψ} → (δ : Subst Θ' Ψ) → Unifies¹ e (⟦ X /ᵉ i ∷ τ ⟧ᴬ ⨟ˢ δ)
         → Unifies¹ (e [ X forᵉ i ]ᴱ) (⟦ τ ⟧ᴬ ⨟ˢ δ)
    down δ u = Unifies¹-[]ᴱ⁻ e (X forᵉ i) (⟦ τ ⟧ᴬ ⨟ˢ δ)
                 (Unifies¹-resp-≐ˢ (⨟ˢ-assoc (X forᵉ i) ⟦ τ ⟧ᴬ δ) e u)

    yes' : ∀ {Θ''} {ρ'' : AList (Θ +e) Θ''} → mmap (consᵉ X i) m ≡ just (Θ'' , ρ'')
         → Max (Uni e) (X /ᵉ i ∷ τ) ρ''
    yes' q with map-just (consᵉ X i) m q
    ... | (Θ₂ , τ') , q' , refl = max (λ δ u →
            let r = fact (onJust s q') δ (down δ u)
            in proj₁ r , glueᵉ X i τ τ' δ (proj₁ r) (proj₂ r))

    no' : mmap (consᵉ X i) m ≡ nothing → ∀ {Ψ} → (δ : Subst Θ' Ψ)
        → Fixing rg (⟦ X /ᵉ i ∷ τ ⟧ᴬ ⨟ˢ δ) → ¬ Unifies¹ e (⟦ X /ᵉ i ∷ τ ⟧ᴬ ⨟ˢ δ)
    no' q δ fx u = onNothing s (map-nothing (consᵉ X i) m q) δ (Fixing-∷ᵉ X i τ δ fx) (down δ u)

--------------------------------------------------------------
-- A variable that occurs is no larger than its host         --
--------------------------------------------------------------

occ≤ᵉ : ∀ {Θ Ψ} → (i : EVar Θ) → (ε : EExp Θ) → (σ : Subst Θ Ψ) → occᵉ-e i ε ≡ true
      → sizeᵉ (sE σ i) ≤ sizeᵉ (ε [ σ ]ᵉ)
occ≤ᵉ i (evar j)   σ q = subst (λ z → sizeᵉ (sE σ i) ≤ sizeᵉ (sE σ z)) (true-dec (i ≟ᶠ j) q) ≤-refl
occ≤ᵉ i (econst c) σ ()
occ≤ᵉ i (ε ·̂ₑ ε')  σ q with ∨-true (occᵉ-e i ε) (occᵉ-e i ε') q
... | inj₁ r = m≤n⇒m≤1+n (≤-trans (occ≤ᵉ i ε σ r) (m≤m+n _ _))
... | inj₂ r = m≤n⇒m≤1+n (≤-trans (occ≤ᵉ i ε' σ r) (m≤n+m _ _))

occ≤ʳ : ∀ {Θ Ψ} → (i : RVar Θ) → (ρ : RExp Θ) → (σ : Subst Θ Ψ) → occʳ-r i ρ ≡ true
      → sizeʳ (sR σ i) ≤ sizeʳ (ρ [ σ ]ʳ)
occ≤ʳ i (rvar j)   σ q = subst (λ z → sizeʳ (sR σ i) ≤ sizeʳ (sR σ z)) (true-dec (i ≟ᶠ j) q) ≤-refl
occ≤ʳ i (rconst c) σ ()
occ≤ʳ i (ρ ·̂ᵣ ρ')  σ q with ∨-true (occʳ-r i ρ) (occʳ-r i ρ') q
... | inj₁ r = m≤n⇒m≤1+n (≤-trans (occ≤ʳ i ρ σ r) (m≤m+n _ _))
... | inj₂ r = m≤n⇒m≤1+n (≤-trans (occ≤ʳ i ρ' σ r) (m≤n+m _ _))
occ≤ʳ i ∣ ε ∣̂ᵉ     σ ()

mutual

  occ≤ᵛ : ∀ {Θ Ψ} → (α : TyVar Θ) → (A : OVType Θ) → (σ : Subst Θ Ψ) → occᵗ-v α A ≡ true
        → sizeᵛ (sTy σ α) ≤ sizeᵛ (A [ σ ]ᵛ)
  occ≤ᵛ α (tvar β) σ q =
    subst (λ z → sizeᵛ (sTy σ α) ≤ sizeᵛ (sTy σ z)) (true-dec (α ≟ᶠ β) q) ≤-refl
  occ≤ᵛ α (Base b)  σ ()
  occ≤ᵛ α Unit      σ ()
  occ≤ᵛ α Bool      σ ()
  occ≤ᵛ α (A |×| B) σ q with ∨-true (occᵗ-v α A) (occᵗ-v α B) q
  ... | inj₁ r = m≤n⇒m≤1+n (≤-trans (occ≤ᵛ α A σ r) (m≤m+n _ _))
  ... | inj₂ r = m≤n⇒m≤1+n (≤-trans (occ≤ᵛ α B σ r) (m≤n+m _ _))
  occ≤ᵛ α Empty     σ ()
  occ≤ᵛ α (A ⇒ C)   σ q with ∨-true (occᵗ-v α A) (occᵗ-c α C) q
  ... | inj₁ r = m≤n⇒m≤1+n (≤-trans (occ≤ᵛ α A σ r) (m≤m+n _ _))
  ... | inj₂ r = m≤n⇒m≤1+n (≤-trans (occ≤ᶜ α C σ r) (m≤n+m _ _))
  occ≤ᵛ α ([ ρ ] A) σ q = m≤n⇒m≤1+n (≤-trans (occ≤ᵛ α A σ q) (m≤n+m _ _))

  occ≤ᶜ : ∀ {Θ Ψ} → (α : TyVar Θ) → (C : OCType Θ) → (σ : Subst Θ Ψ) → occᵗ-c α C ≡ true
        → sizeᵛ (sTy σ α) ≤ sizeᶜ (C [ σ ]ᶜ)
  occ≤ᶜ α (A ‼ ε) σ q = m≤n⇒m≤1+n (≤-trans (occ≤ᵛ α A σ q) (m≤m+n _ _))

--------------------------------------------------------------
-- A proper occurrence is a strict increase, and hence a     --
-- refutation of the equation that demanded it               --
--------------------------------------------------------------

no-cycleᵉ : ∀ {Θ Ψ} → (i : EVar Θ) → (ε : EExp Θ) → (σ : Subst Θ Ψ) → ¬ (ε ≡ evar i)
          → occᵉ-e i ε ≡ true → ¬ (sE σ i ≡ ε [ σ ]ᵉ)
no-cycleᵉ i (evar j) σ nv q u = nv (cong evar (sym (true-dec (i ≟ᶠ j) q)))
no-cycleᵉ i (econst c) σ nv () u
no-cycleᵉ i (ε ·̂ₑ ε') σ nv q u
  with ∨-true (occᵉ-e i ε) (occᵉ-e i ε') q
... | inj₁ r = 1+n≰n (subst (suc (sizeᵉ (sE σ i)) ≤_) (sym (cong sizeᵉ u))
                            (s≤s (≤-trans (occ≤ᵉ i ε σ r) (m≤m+n _ _))))
... | inj₂ r = 1+n≰n (subst (suc (sizeᵉ (sE σ i)) ≤_) (sym (cong sizeᵉ u))
                            (s≤s (≤-trans (occ≤ᵉ i ε' σ r) (m≤n+m _ _))))

no-cycleʳ : ∀ {Θ Ψ} → (i : RVar Θ) → (ρ : RExp Θ) → (σ : Subst Θ Ψ) → ¬ (ρ ≡ rvar i)
          → occʳ-r i ρ ≡ true → ¬ (sR σ i ≡ ρ [ σ ]ʳ)
no-cycleʳ i (rvar j) σ nv q u = nv (cong rvar (sym (true-dec (i ≟ᶠ j) q)))
no-cycleʳ i (rconst c) σ nv () u
no-cycleʳ i (ρ ·̂ᵣ ρ') σ nv q u
  with ∨-true (occʳ-r i ρ) (occʳ-r i ρ') q
... | inj₁ r = 1+n≰n (subst (suc (sizeʳ (sR σ i)) ≤_) (sym (cong sizeʳ u))
                            (s≤s (≤-trans (occ≤ʳ i ρ σ r) (m≤m+n _ _))))
... | inj₂ r = 1+n≰n (subst (suc (sizeʳ (sR σ i)) ≤_) (sym (cong sizeʳ u))
                            (s≤s (≤-trans (occ≤ʳ i ρ' σ r) (m≤n+m _ _))))
no-cycleʳ i ∣ ε ∣̂ᵉ σ nv () u

no-cycleᵛ : ∀ {Θ Ψ} → (α : TyVar Θ) → (A : OVType Θ) → (σ : Subst Θ Ψ) → ¬ (A ≡ tvar α)
          → occᵗ-v α A ≡ true → ¬ (sTy σ α ≡ A [ σ ]ᵛ)
no-cycleᵛ α (tvar β) σ nv q u = nv (cong tvar (sym (true-dec (α ≟ᶠ β) q)))
no-cycleᵛ α (Base b) σ nv () u
no-cycleᵛ α Unit σ nv () u
no-cycleᵛ α Bool σ nv () u
no-cycleᵛ α (A |×| B) σ nv q u with ∨-true (occᵗ-v α A) (occᵗ-v α B) q
... | inj₁ r = 1+n≰n (subst (suc (sizeᵛ (sTy σ α)) ≤_) (sym (cong sizeᵛ u))
                            (s≤s (≤-trans (occ≤ᵛ α A σ r) (m≤m+n _ _))))
... | inj₂ r = 1+n≰n (subst (suc (sizeᵛ (sTy σ α)) ≤_) (sym (cong sizeᵛ u))
                            (s≤s (≤-trans (occ≤ᵛ α B σ r) (m≤n+m _ _))))
no-cycleᵛ α Empty σ nv () u
no-cycleᵛ α (A ⇒ C) σ nv q u with ∨-true (occᵗ-v α A) (occᵗ-c α C) q
... | inj₁ r = 1+n≰n (subst (suc (sizeᵛ (sTy σ α)) ≤_) (sym (cong sizeᵛ u))
                            (s≤s (≤-trans (occ≤ᵛ α A σ r) (m≤m+n _ _))))
... | inj₂ r = 1+n≰n (subst (suc (sizeᵛ (sTy σ α)) ≤_) (sym (cong sizeᵛ u))
                            (s≤s (≤-trans (occ≤ᶜ α C σ r) (m≤n+m _ _))))
no-cycleᵛ α ([ ρ ] A) σ nv q u =
  1+n≰n (subst (suc (sizeᵛ (sTy σ α)) ≤_) (sym (cong sizeᵛ u))
               (s≤s (≤-trans (occ≤ᵛ α A σ q) (m≤n+m _ _))))

--------------------------------------------------------------
-- Two substitutions that agree away from a variable agree   --
-- on every expression the variable misses                   --
--------------------------------------------------------------

awayᵉ : ∀ {Θ Ψ} → (i : EVar Θ) → (σ δ : Subst Θ Ψ)
      → ((j : EVar Θ) → ¬ (i ≡ j) → sE σ j ≡ sE δ j)
      → (ε : EExp Θ) → occᵉ-e i ε ≡ false → ε [ σ ]ᵉ ≡ ε [ δ ]ᵉ
awayᵉ i σ δ h (evar j)   o = h j (dec-false (i ≟ᶠ j) o)
awayᵉ i σ δ h (econst c) o = refl
awayᵉ i σ δ h (ε ·̂ₑ ε')  o with ∨-false (occᵉ-e i ε) (occᵉ-e i ε') o
... | o₁ , o₂ = cong₂ _·̂ₑ_ (awayᵉ i σ δ h ε o₁) (awayᵉ i σ δ h ε' o₂)

awayʳ : ∀ {Θ Ψ} → (i : RVar Θ) → (σ δ : Subst Θ Ψ)
      → ((j : RVar Θ) → ¬ (i ≡ j) → sR σ j ≡ sR δ j)
      → ((j : EVar Θ) → sE σ j ≡ sE δ j)
      → (ρ : RExp Θ) → occʳ-r i ρ ≡ false → ρ [ σ ]ʳ ≡ ρ [ δ ]ʳ
awayʳ i σ δ h he (rvar j)   o = h j (dec-false (i ≟ᶠ j) o)
awayʳ i σ δ h he (rconst c) o = refl
awayʳ i σ δ h he (ρ ·̂ᵣ ρ')  o with ∨-false (occʳ-r i ρ) (occʳ-r i ρ') o
... | o₁ , o₂ = cong₂ _·̂ᵣ_ (awayʳ i σ δ h he ρ o₁) (awayʳ i σ δ h he ρ' o₂)
awayʳ i σ δ h he ∣ ε ∣̂ᵉ     o = cong ∣_∣̂ᵉ (agreeᵉ he ε)

mutual

  awayᵛ : ∀ {Θ Ψ} → (α : TyVar Θ) → (σ δ : Subst Θ Ψ)
        → ((β : TyVar Θ) → ¬ (α ≡ β) → sTy σ β ≡ sTy δ β)
        → ((i : RVar Θ) → sR σ i ≡ sR δ i)
        → ((i : EVar Θ) → sE σ i ≡ sE δ i)
        → (A : OVType Θ) → occᵗ-v α A ≡ false → A [ σ ]ᵛ ≡ A [ δ ]ᵛ
  awayᵛ α σ δ h hr he (tvar β)  o = h β (dec-false (α ≟ᶠ β) o)
  awayᵛ α σ δ h hr he (Base b)  o = refl
  awayᵛ α σ δ h hr he Unit      o = refl
  awayᵛ α σ δ h hr he Bool      o = refl
  awayᵛ α σ δ h hr he (A |×| B) o with ∨-false (occᵗ-v α A) (occᵗ-v α B) o
  ... | o₁ , o₂ = cong₂ _|×|_ (awayᵛ α σ δ h hr he A o₁) (awayᵛ α σ δ h hr he B o₂)
  awayᵛ α σ δ h hr he Empty     o = refl
  awayᵛ α σ δ h hr he (A ⇒ C)   o with ∨-false (occᵗ-v α A) (occᵗ-c α C) o
  ... | o₁ , o₂ = cong₂ _⇒_ (awayᵛ α σ δ h hr he A o₁) (awayᶜ α σ δ h hr he C o₂)
  awayᵛ α σ δ h hr he ([ ρ ] A) o =
    cong₂ [_]_ (agreeʳ hr he ρ) (awayᵛ α σ δ h hr he A o)

  awayᶜ : ∀ {Θ Ψ} → (α : TyVar Θ) → (σ δ : Subst Θ Ψ)
        → ((β : TyVar Θ) → ¬ (α ≡ β) → sTy σ β ≡ sTy δ β)
        → ((i : RVar Θ) → sR σ i ≡ sR δ i)
        → ((i : EVar Θ) → sE σ i ≡ sE δ i)
        → (C : OCType Θ) → occᵗ-c α C ≡ false → C [ σ ]ᶜ ≡ C [ δ ]ᶜ
  awayᶜ α σ δ h hr he (A ‼ ε) o = cong₂ _‼_ (awayᵛ α σ δ h hr he A o) (agreeᵉ he ε)

--------------------------------------------------------------
-- Binding a variable is maximal                             --
--                                                           --
-- A substitution solving the equation is recovered from the  --
-- store by restricting it along the thinning of the bound    --
-- variable.                                                  --
--------------------------------------------------------------

bindᵗ-max : ∀ {Θ} → (α : TyVar (Θ +ty)) → (A : OVType (Θ +ty)) → occᵗ-v α A ≡ false
          → Max (Uni (eqᵛ (tvar α) A)) anil ((A [ Unit forᵗ α ]ᵛ) /ᵗ α ∷ anil)
bindᵗ-max {Θ} α A o = max lem
  where
    lem : ∀ {Ψ} → (δ : Subst (Θ +ty) Ψ) → at (Uni (eqᵛ (tvar α) A) ⋄ ⟦ anil ⟧ᴬ) δ
        → Σ[ δ' ∈ Subst Θ Ψ ]
            ((⟦ (A [ Unit forᵗ α ]ᵛ) /ᵗ α ∷ anil ⟧ᴬ ⨟ˢ δ') ≐ˢ (⟦ anil ⟧ᴬ ⨟ˢ δ))
    lem {Ψ} δ u = δ' , mk≐ˢ ty (λ i → refl) (λ i → refl)
      where
        δ' : Subst Θ Ψ
        δ' = sub (λ β → sTy δ (thinᵗ {Θ} α β)) (λ i → sR δ i) (λ i → sE δ i)

        miss : (β : TyVar (Θ +ty)) → ¬ (α ≡ β) → sTy ((Unit forᵗ α) ⨟ˢ δ') β ≡ sTy δ β
        miss β ne with thick-¬ {nTy Θ} α β ne
        ... | β' , r = trans (cong (λ z → (maybe′ tvar (Unit {Θ}) z) [ δ' ]ᵛ) r)
                             (cong (sTy δ) (sym (thick-just {nTy Θ} α β β' r)))

        hit : (A [ Unit forᵗ α ]ᵛ) [ δ' ]ᵛ ≡ A [ δ ]ᵛ
        hit = trans ([⨟]ᵛ A (Unit forᵗ α) δ')
                    (awayᵛ α ((Unit forᵗ α) ⨟ˢ δ') δ miss (λ i → refl) (λ i → refl) A o)

        ty : (β : TyVar (Θ +ty))
           → sTy (⟦ (A [ Unit forᵗ α ]ᵛ) /ᵗ α ∷ anil ⟧ᴬ ⨟ˢ δ') β ≡ sTy (⟦ anil ⟧ᴬ ⨟ˢ δ) β
        ty β with α ≟ᶠ β
        ... | yes refl =
              trans (cong (λ z → ((maybe′ tvar (A [ Unit forᵗ α ]ᵛ) z) [ idˢ ]ᵛ) [ δ' ]ᵛ)
                          (thick-refl {nTy Θ} α))
              (trans (cong (_[ δ' ]ᵛ) ([id]ᵛ (A [ Unit forᵗ α ]ᵛ)))
                     (trans hit (sym u)))
        ... | no ne with thick-¬ {nTy Θ} α β ne
        ...   | β' , r =
                trans (cong (λ z → ((maybe′ tvar (A [ Unit forᵗ α ]ᵛ) z) [ idˢ ]ᵛ) [ δ' ]ᵛ) r)
                      (cong (sTy δ) (sym (thick-just {nTy Θ} α β β' r)))

bindʳ-max : ∀ {Θ} → (i : RVar (Θ +r)) → (ρ : RExp (Θ +r)) → occʳ-r i ρ ≡ false
          → Max (Uni (eqʳ (rvar i) ρ)) anil ((ρ [ ûᵣ forʳ i ]ʳ) /ʳ i ∷ anil)
bindʳ-max {Θ} i ρ o = max lem
  where
    lem : ∀ {Ψ} → (δ : Subst (Θ +r) Ψ) → at (Uni (eqʳ (rvar i) ρ) ⋄ ⟦ anil ⟧ᴬ) δ
        → Σ[ δ' ∈ Subst Θ Ψ ]
            ((⟦ (ρ [ ûᵣ forʳ i ]ʳ) /ʳ i ∷ anil ⟧ᴬ ⨟ˢ δ') ≐ˢ (⟦ anil ⟧ᴬ ⨟ˢ δ))
    lem {Ψ} δ u = δ' , mk≐ˢ (λ α → refl) gr (λ j → refl)
      where
        δ' : Subst Θ Ψ
        δ' = sub (λ α → sTy δ α) (λ j → sR δ (thinʳ {Θ} i j)) (λ j → sE δ j)

        miss : (j : RVar (Θ +r)) → ¬ (i ≡ j) → sR ((ûᵣ forʳ i) ⨟ˢ δ') j ≡ sR δ j
        miss j ne with thick-¬ {nR Θ} i j ne
        ... | j' , r = trans (cong (λ z → (maybe′ rvar (ûᵣ {Θ}) z) [ δ' ]ʳ) r)
                             (cong (sR δ) (sym (thick-just {nR Θ} i j j' r)))

        hit : (ρ [ ûᵣ forʳ i ]ʳ) [ δ' ]ʳ ≡ ρ [ δ ]ʳ
        hit = trans ([⨟]ʳ ρ (ûᵣ forʳ i) δ')
                    (awayʳ i ((ûᵣ forʳ i) ⨟ˢ δ') δ miss (λ j → refl) ρ o)

        gr : (j : RVar (Θ +r))
           → sR (⟦ (ρ [ ûᵣ forʳ i ]ʳ) /ʳ i ∷ anil ⟧ᴬ ⨟ˢ δ') j ≡ sR (⟦ anil ⟧ᴬ ⨟ˢ δ) j
        gr j with i ≟ᶠ j
        ... | yes refl =
              trans (cong (λ z → ((maybe′ rvar (ρ [ ûᵣ forʳ i ]ʳ) z) [ idˢ ]ʳ) [ δ' ]ʳ)
                          (thick-refl {nR Θ} i))
              (trans (cong (_[ δ' ]ʳ) ([id]ʳ (ρ [ ûᵣ forʳ i ]ʳ)))
                     (trans hit (sym u)))
        ... | no ne with thick-¬ {nR Θ} i j ne
        ...   | j' , r =
                trans (cong (λ z → ((maybe′ rvar (ρ [ ûᵣ forʳ i ]ʳ) z) [ idˢ ]ʳ) [ δ' ]ʳ) r)
                      (cong (sR δ) (sym (thick-just {nR Θ} i j j' r)))

bindᵉ-max : ∀ {Θ} → (i : EVar (Θ +e)) → (ε : EExp (Θ +e)) → occᵉ-e i ε ≡ false
          → Max (Uni (eqᵉ (evar i) ε)) anil ((ε [ ûₑ forᵉ i ]ᵉ) /ᵉ i ∷ anil)
bindᵉ-max {Θ} i ε o = max lem
  where
    lem : ∀ {Ψ} → (δ : Subst (Θ +e) Ψ) → at (Uni (eqᵉ (evar i) ε) ⋄ ⟦ anil ⟧ᴬ) δ
        → Σ[ δ' ∈ Subst Θ Ψ ]
            ((⟦ (ε [ ûₑ forᵉ i ]ᵉ) /ᵉ i ∷ anil ⟧ᴬ ⨟ˢ δ') ≐ˢ (⟦ anil ⟧ᴬ ⨟ˢ δ))
    lem {Ψ} δ u = δ' , mk≐ˢ (λ α → refl) (λ j → refl) ge
      where
        δ' : Subst Θ Ψ
        δ' = sub (λ α → sTy δ α) (λ j → sR δ j) (λ j → sE δ (thinᵉ {Θ} i j))

        miss : (j : EVar (Θ +e)) → ¬ (i ≡ j) → sE ((ûₑ forᵉ i) ⨟ˢ δ') j ≡ sE δ j
        miss j ne with thick-¬ {nE Θ} i j ne
        ... | j' , r = trans (cong (λ z → (maybe′ evar (ûₑ {Θ}) z) [ δ' ]ᵉ) r)
                             (cong (sE δ) (sym (thick-just {nE Θ} i j j' r)))

        hit : (ε [ ûₑ forᵉ i ]ᵉ) [ δ' ]ᵉ ≡ ε [ δ ]ᵉ
        hit = trans ([⨟]ᵉ ε (ûₑ forᵉ i) δ')
                    (awayᵉ i ((ûₑ forᵉ i) ⨟ˢ δ') δ miss ε o)

        ge : (j : EVar (Θ +e))
           → sE (⟦ (ε [ ûₑ forᵉ i ]ᵉ) /ᵉ i ∷ anil ⟧ᴬ ⨟ˢ δ') j ≡ sE (⟦ anil ⟧ᴬ ⨟ˢ δ) j
        ge j with i ≟ᶠ j
        ... | yes refl =
              trans (cong (λ z → ((maybe′ evar (ε [ ûₑ forᵉ i ]ᵉ) z) [ idˢ ]ᵉ) [ δ' ]ᵉ)
                          (thick-refl {nE Θ} i))
              (trans (cong (_[ δ' ]ᵉ) ([id]ᵉ (ε [ ûₑ forᵉ i ]ᵉ)))
                     (trans hit (sym u)))
        ... | no ne with thick-¬ {nE Θ} i j ne
        ...   | j' , r =
                trans (cong (λ z → ((maybe′ evar (ε [ ûₑ forᵉ i ]ᵉ) z) [ idˢ ]ᵉ) [ δ' ]ᵉ) r)
                      (cong (sE δ) (sym (thick-just {nE Θ} i j j' r)))

--------------------------------------------------------------
-- Reading the verdict of a binding attempt                  --
--------------------------------------------------------------

flexᵗ-inv : ∀ {Θ} → (α : TyVar Θ) → (A : OVType Θ) → {Θ'' : Scope} → {ρ'' : AList Θ Θ''}
          → flexᵗ α A ≡ just (Θ'' , ρ'') → Max (Uni (eqᵛ (tvar α) A)) anil ρ''
flexᵗ-inv {scope (suc nt) nr ne} α A eq
  with map-just (λ A' → scope nt nr ne , A' /ᵗ α ∷ anil) (chkᵗ-v {scope nt nr ne} α A) eq
... | A' , q , refl with if-inv (occᵗ-v α A) (A [ Unit forᵗ α ]ᵛ) q
...   | o , r = subst (λ z → Max (Uni (eqᵛ (tvar α) A)) anil (z /ᵗ α ∷ anil)) r
                      (bindᵗ-max α A o)

flexᵗ-no : ∀ {Θ} → (α : TyVar Θ) → (A : OVType Θ) → flexᵗ α A ≡ nothing → occᵗ-v α A ≡ true
flexᵗ-no {scope (suc nt) nr ne} α A eq =
  if-nothing (occᵗ-v α A) (A [ Unit forᵗ α ]ᵛ)
             (map-nothing (λ A' → scope nt nr ne , A' /ᵗ α ∷ anil)
                          (chkᵗ-v {scope nt nr ne} α A) eq)

flexʳ-inv : ∀ {Θ} → (i : RVar Θ) → (ρ : RExp Θ) → {Θ'' : Scope} → {ρ'' : AList Θ Θ''}
          → flexʳ i ρ ≡ just (Θ'' , ρ'') → Max (Uni (eqʳ (rvar i) ρ)) anil ρ''
flexʳ-inv {scope nt (suc nr) ne} i ρ eq
  with map-just (λ X → scope nt nr ne , X /ʳ i ∷ anil) (chkʳ-r {scope nt nr ne} i ρ) eq
... | X , q , refl with if-inv (occʳ-r i ρ) (ρ [ ûᵣ forʳ i ]ʳ) q
...   | o , r = subst (λ z → Max (Uni (eqʳ (rvar i) ρ)) anil (z /ʳ i ∷ anil)) r
                      (bindʳ-max i ρ o)

flexʳ-no : ∀ {Θ} → (i : RVar Θ) → (ρ : RExp Θ) → flexʳ i ρ ≡ nothing → occʳ-r i ρ ≡ true
flexʳ-no {scope nt (suc nr) ne} i ρ eq =
  if-nothing (occʳ-r i ρ) (ρ [ ûᵣ forʳ i ]ʳ)
             (map-nothing (λ X → scope nt nr ne , X /ʳ i ∷ anil)
                          (chkʳ-r {scope nt nr ne} i ρ) eq)

flexᵉ-inv : ∀ {Θ} → (rg : Rig Θ) → (i : EVar Θ) → (ε : EExp Θ)
          → {Θ'' : Scope} → {ρ'' : AList Θ Θ''}
          → flexᵉ rg i ε ≡ just (Θ'' , ρ'') → Max (Uni (eqᵉ (evar i) ε)) anil ρ''
flexᵉ-inv {scope nt nr (suc ne)} rg i ε eq
  with if-else (i ∈ᶠ rg)
               (mmap (λ X → scope nt nr ne , X /ᵉ i ∷ anil) (chkᵉ-e {scope nt nr ne} i ε)) eq
... | eq' with map-just (λ X → scope nt nr ne , X /ᵉ i ∷ anil) (chkᵉ-e {scope nt nr ne} i ε) eq'
...   | X , q , refl with if-inv (occᵉ-e i ε) (ε [ ûₑ forᵉ i ]ᵉ) q
...     | o , r = subst (λ z → Max (Uni (eqᵉ (evar i) ε)) anil (z /ᵉ i ∷ anil)) r
                        (bindᵉ-max i ε o)

flexᵉ-no : ∀ {Θ} → (rg : Rig Θ) → (i : EVar Θ) → (ε : EExp Θ) → flexᵉ rg i ε ≡ nothing
         → (i ∈ᶠ rg ≡ true) ⊎ (occᵉ-e i ε ≡ true)
flexᵉ-no {scope nt nr (suc ne)} rg i ε eq
  with if-no (i ∈ᶠ rg)
             (mmap (λ X → scope nt nr ne , X /ᵉ i ∷ anil) (chkᵉ-e {scope nt nr ne} i ε)) eq
... | inj₁ r = inj₁ r
... | inj₂ q = inj₂ (if-nothing (occᵉ-e i ε) (ε [ ûₑ forᵉ i ]ᵉ)
                                (map-nothing (λ X → scope nt nr ne , X /ᵉ i ∷ anil)
                                             (chkᵉ-e {scope nt nr ne} i ε) q))

--------------------------------------------------------------
-- Binding a variable to a non-variable                      --
--------------------------------------------------------------

data NonVarᵉ {Θ : Scope} : EExp Θ → Set where
  nvconstᵉ : (c : E) → NonVarᵉ (econst c)
  nvmulᵉ   : (ε ε' : EExp Θ) → NonVarᵉ (ε ·̂ₑ ε')

nonvarᵉ-≢ : ∀ {Θ} {ε : EExp Θ} {i : EVar Θ} → NonVarᵉ ε → ¬ (ε ≡ evar i)
nonvarᵉ-≢ (nvconstᵉ c)  ()
nonvarᵉ-≢ (nvmulᵉ ε ε') ()

-- A rigid variable goes to a variable, and a non-variable does not

rigidᵉ-no : ∀ {Θ Ψ} {ε : EExp Θ} {δ : Subst Θ Ψ} {i : EVar Θ} → NonVarᵉ ε
          → Σ[ k ∈ EVar Ψ ] (sE δ i ≡ evar k) → ¬ (sE δ i ≡ ε [ δ ]ᵉ)
rigidᵉ-no (nvconstᵉ c)  (k , s) u with trans (sym s) u
... | ()
rigidᵉ-no (nvmulᵉ ε ε') (k , s) u with trans (sym s) u
... | ()

--------------------------------------------------------------
-- The specification of a binding attempt                    --
--------------------------------------------------------------

flexᵗ-spec : ∀ {Θ} → (rg : Rig Θ) → (α : TyVar Θ) → (A : OVType Θ) → ¬ (A ≡ tvar α)
           → Spec rg (Uni (eqᵛ (tvar α) A)) anil (flexᵗ α A)
flexᵗ-spec rg α A na =
  spec (flexᵗ-inv α A) (λ eq δ fx → no-cycleᵛ α A δ na (flexᵗ-no α A eq))

flexʳ-spec : ∀ {Θ} → (rg : Rig Θ) → (i : RVar Θ) → (ρ : RExp Θ) → ¬ (ρ ≡ rvar i)
           → Spec rg (Uni (eqʳ (rvar i) ρ)) anil (flexʳ i ρ)
flexʳ-spec rg i ρ na =
  spec (flexʳ-inv i ρ) (λ eq δ fx → no-cycleʳ i ρ δ na (flexʳ-no i ρ eq))

flexᵉ-spec : ∀ {Θ} → (rg : Rig Θ) → (i : EVar Θ) → (ε : EExp Θ) → NonVarᵉ ε
           → Spec rg (Uni (eqᵉ (evar i) ε)) anil (flexᵉ rg i ε)
flexᵉ-spec rg i ε nv = spec (flexᵉ-inv rg i ε) no'
  where
    no' : flexᵉ rg i ε ≡ nothing → ∀ {Ψ} → (δ : Subst _ Ψ)
        → Fixing rg (⟦ anil ⟧ᴬ ⨟ˢ δ) → ¬ Unifies¹ (eqᵉ (evar i) ε) (⟦ anil ⟧ᴬ ⨟ˢ δ)
    no' eq δ fx u with flexᵉ-no rg i ε eq
    ... | inj₁ r = rigidᵉ-no nv (fixᵉ fx i r) u
    ... | inj₂ o = no-cycleᵉ i ε δ (nonvarᵉ-≢ nv) o u

--------------------------------------------------------------
-- The specification of a flexible-flexible verdict          --
--------------------------------------------------------------

flexFlexᵗ-spec : ∀ {Θ} → (rg : Rig Θ) → (α β : TyVar Θ)
               → Spec rg (Uni (eqᵛ (tvar α) (tvar β))) anil (flexFlexᵗ α β)
flexFlexᵗ-spec {Θ} rg α β = spec yes' no'
  where
    yes' : ∀ {Θ''} {ρ'' : AList Θ Θ''} → flexFlexᵗ α β ≡ just (Θ'' , ρ'')
         → Max (Uni (eqᵛ (tvar α) (tvar β))) anil ρ''
    yes' eq with dec-if (α ≟ᶠ β) (just (Θ , anil)) (flexᵗ α (tvar β)) eq
    ... | inj₁ (r , refl) = Max-id
    ... | inj₂ q          = flexᵗ-inv α (tvar β) q

    no' : flexFlexᵗ α β ≡ nothing → ∀ {Ψ} → (δ : Subst Θ Ψ) → Fixing rg (⟦ anil ⟧ᴬ ⨟ˢ δ)
        → ¬ Unifies¹ (eqᵛ (tvar α) (tvar β)) (⟦ anil ⟧ᴬ ⨟ˢ δ)
    no' eq δ fx u with dec-if-nothing (α ≟ᶠ β) (just (Θ , anil)) (flexᵗ α (tvar β)) eq
    ... | inj₁ (r , ())
    ... | inj₂ (ne , q) = ne (true-dec (α ≟ᶠ β) (flexᵗ-no α (tvar β) q))

flexFlexʳ-spec : ∀ {Θ} → (rg : Rig Θ) → (i j : RVar Θ)
               → Spec rg (Uni (eqʳ (rvar i) (rvar j))) anil (flexFlexʳ i j)
flexFlexʳ-spec {Θ} rg i j = spec yes' no'
  where
    yes' : ∀ {Θ''} {ρ'' : AList Θ Θ''} → flexFlexʳ i j ≡ just (Θ'' , ρ'')
         → Max (Uni (eqʳ (rvar i) (rvar j))) anil ρ''
    yes' eq with dec-if (i ≟ᶠ j) (just (Θ , anil)) (flexʳ i (rvar j)) eq
    ... | inj₁ (r , refl) = Max-id
    ... | inj₂ q          = flexʳ-inv i (rvar j) q

    no' : flexFlexʳ i j ≡ nothing → ∀ {Ψ} → (δ : Subst Θ Ψ) → Fixing rg (⟦ anil ⟧ᴬ ⨟ˢ δ)
        → ¬ Unifies¹ (eqʳ (rvar i) (rvar j)) (⟦ anil ⟧ᴬ ⨟ˢ δ)
    no' eq δ fx u with dec-if-nothing (i ≟ᶠ j) (just (Θ , anil)) (flexʳ i (rvar j)) eq
    ... | inj₁ (r , ())
    ... | inj₂ (ne , q) = ne (true-dec (i ≟ᶠ j) (flexʳ-no i (rvar j) q))

flexFlexᵉ-spec : ∀ {Θ} → (rg : Rig Θ) → (i j : EVar Θ)
               → Spec rg (Uni (eqᵉ (evar i) (evar j))) anil (flexFlexᵉ rg i j)
flexFlexᵉ-spec {Θ} rg i j = spec yes' no'
  where
    yes' : ∀ {Θ''} {ρ'' : AList Θ Θ''} → flexFlexᵉ rg i j ≡ just (Θ'' , ρ'')
         → Max (Uni (eqᵉ (evar i) (evar j))) anil ρ''
    yes' eq with dec-if (i ≟ᶠ j) (just (Θ , anil))
                        (flexᵉ rg i (evar j) <∣> flexᵉ rg j (evar i)) eq
    ... | inj₁ (r , refl) = Max-id
    ... | inj₂ q with alt-just (flexᵉ rg i (evar j)) (flexᵉ rg j (evar i)) q
    ...   | inj₁ q' = flexᵉ-inv rg i (evar j) q'
    ...   | inj₂ q' = Max-map sym (flexᵉ-inv rg j (evar i) q')

    no' : flexFlexᵉ rg i j ≡ nothing → ∀ {Ψ} → (δ : Subst Θ Ψ) → Fixing rg (⟦ anil ⟧ᴬ ⨟ˢ δ)
        → ¬ Unifies¹ (eqᵉ (evar i) (evar j)) (⟦ anil ⟧ᴬ ⨟ˢ δ)
    no' eq δ fx u with dec-if-nothing (i ≟ᶠ j) (just (Θ , anil))
                                      (flexᵉ rg i (evar j) <∣> flexᵉ rg j (evar i)) eq
    ... | inj₁ (r , ())
    ... | inj₂ (ne , q) with alt-nothing (flexᵉ rg i (evar j)) (flexᵉ rg j (evar i)) q
    ...   | q₁ , q₂ with flexᵉ-no rg i (evar j) q₁ | flexᵉ-no rg j (evar i) q₂
    ...     | inj₁ r₁ | inj₁ r₂ = ne (injᵉ fx i j r₁ r₂ u)
    ...     | inj₁ r₁ | inj₂ r₂ = ne (sym (true-dec (j ≟ᶠ i) r₂))
    ...     | inj₂ r₁ | _       = ne (true-dec (i ≟ᶠ j) r₁)

--------------------------------------------------------------
-- The specification of the unifier                          --
--                                                           --
-- The store-descent clauses are the same for every sort, and --
-- the syntactic clauses are written once per shape of the    --
-- size index, which a clause computes only after. A clash    --
-- needs neither, being a refutation of its own equation.     --
--------------------------------------------------------------

mutual

  amguᵛ-spec : ∀ {Θ Θ'} → (k : ℕ) → (p : Sz Θ ≡ k) → (rg : Rig Θ) → (A B : OVType Θ)
             → (ρ : AList Θ Θ') → Spec rg (Uni (eqᵛ A B)) ρ (amguᵛ k p rg A B (Θ' , ρ))

  amguᶜ-spec : ∀ {Θ Θ'} → (k : ℕ) → (p : Sz Θ ≡ k) → (rg : Rig Θ) → (C D : OCType Θ)
             → (ρ : AList Θ Θ') → Spec rg (Uni (eqᶜ C D)) ρ (amguᶜ k p rg C D (Θ' , ρ))

  amguʳ-spec : ∀ {Θ Θ'} → (k : ℕ) → (p : Sz Θ ≡ k) → (rg : Rig Θ) → (ρ₀ ρ₁ : RExp Θ)
             → (ρ : AList Θ Θ') → Spec rg (Uni (eqʳ ρ₀ ρ₁)) ρ (amguʳ k p rg ρ₀ ρ₁ (Θ' , ρ))

  amguᵉ-spec : ∀ {Θ Θ'} → (k : ℕ) → (p : Sz Θ ≡ k) → (rg : Rig Θ) → (ε ε' : EExp Θ)
             → (ρ : AList Θ Θ') → Spec rg (Uni (eqᵉ ε ε')) ρ (amguᵉ k p rg ε ε' (Θ' , ρ))

  -- value types

  amguᵛ-spec (suc k) p rg A B (X /ᵗ α ∷ τ) =
    descᵗ-spec X α rg (eqᵛ A B) τ
      (amguᵛ-spec k (szᵗ τ p) rg (A [ X forᵗ α ]ᵛ) (B [ X forᵗ α ]ᵛ) τ)
  amguᵛ-spec (suc k) p rg A B (X /ʳ i ∷ τ) =
    descʳ-spec X i rg (eqᵛ A B) τ
      (amguᵛ-spec k (szʳ τ p) rg (A [ X forʳ i ]ᵛ) (B [ X forʳ i ]ᵛ) τ)
  amguᵛ-spec (suc k) p rg A B (X /ᵉ i ∷ τ) =
    descᵉ-spec X i rg (eqᵛ A B) τ
      (amguᵛ-spec k (szᵉ τ p) (popʳᵍ τ i rg) (A [ X forᵉ i ]ᵛ) (B [ X forᵉ i ]ᵛ) τ)
  amguᵛ-spec zero p rg A B (X /ᵗ α ∷ τ) = sz0ᵗ τ p
  amguᵛ-spec zero p rg A B (X /ʳ i ∷ τ) = sz0ʳ τ p
  amguᵛ-spec zero p rg A B (X /ᵉ i ∷ τ) = sz0ᵉ τ p
  amguᵛ-spec (suc k) p rg (tvar α) (tvar β) anil = flexFlexᵗ-spec rg α β
  amguᵛ-spec (suc k) p rg (tvar α) (Base b') anil = flexᵗ-spec rg α (Base b') (λ ())
  amguᵛ-spec (suc k) p rg (tvar α) Unit anil = flexᵗ-spec rg α Unit (λ ())
  amguᵛ-spec (suc k) p rg (tvar α) Bool anil = flexᵗ-spec rg α Bool (λ ())
  amguᵛ-spec (suc k) p rg (tvar α) (B |×| B') anil = flexᵗ-spec rg α (B |×| B') (λ ())
  amguᵛ-spec (suc k) p rg (tvar α) Empty anil = flexᵗ-spec rg α Empty (λ ())
  amguᵛ-spec (suc k) p rg (tvar α) (B ⇒ D) anil = flexᵗ-spec rg α (B ⇒ D) (λ ())
  amguᵛ-spec (suc k) p rg (tvar α) ([ ρ' ] B) anil = flexᵗ-spec rg α ([ ρ' ] B) (λ ())
  amguᵛ-spec (suc k) p rg (Base b) (tvar β) anil = Spec-map sym (flexᵗ-spec rg β (Base b) (λ ()))
  amguᵛ-spec (suc k) p rg Unit (tvar β) anil = Spec-map sym (flexᵗ-spec rg β Unit (λ ()))
  amguᵛ-spec (suc k) p rg Bool (tvar β) anil = Spec-map sym (flexᵗ-spec rg β Bool (λ ()))
  amguᵛ-spec (suc k) p rg (A |×| A') (tvar β) anil = Spec-map sym (flexᵗ-spec rg β (A |×| A') (λ ()))
  amguᵛ-spec (suc k) p rg Empty (tvar β) anil = Spec-map sym (flexᵗ-spec rg β Empty (λ ()))
  amguᵛ-spec (suc k) p rg (A ⇒ C) (tvar β) anil = Spec-map sym (flexᵗ-spec rg β (A ⇒ C) (λ ()))
  amguᵛ-spec (suc k) p rg ([ ρ ] A) (tvar β) anil = Spec-map sym (flexᵗ-spec rg β ([ ρ ] A) (λ ()))
  amguᵛ-spec (suc k) p rg (Base b) (Base b') anil = const-spec (b ≡ᵇ? b') (λ δ u → Base-inj u)
  amguᵛ-spec (suc k) p rg Unit Unit anil = keep
  amguᵛ-spec (suc k) p rg Bool Bool anil = keep
  amguᵛ-spec (suc k) p rg Empty Empty anil = keep
  amguᵛ-spec {Θ} (suc k) p rg (A |×| A') (B |×| B') anil =
    seq-spec (amguᵛ (suc k) p rg A B (Θ , anil)) (amguᵛ (suc k) p rg A' B')
             (amguᵛ-spec (suc k) p rg A B anil) (amguᵛ-spec (suc k) p rg A' B')
             (λ u → ×-inj u)
  amguᵛ-spec {Θ} (suc k) p rg (A ⇒ C) (B ⇒ D) anil =
    seq-spec (amguᵛ (suc k) p rg A B (Θ , anil)) (amguᶜ (suc k) p rg C D)
             (amguᵛ-spec (suc k) p rg A B anil) (amguᶜ-spec (suc k) p rg C D)
             (λ u → ⇒-inj u)
  amguᵛ-spec {Θ} (suc k) p rg ([ ρ ] A) ([ ρ' ] B) anil =
    seq-spec (amguʳ (suc k) p rg ρ ρ' (Θ , anil)) (amguᵛ (suc k) p rg A B)
             (amguʳ-spec (suc k) p rg ρ ρ' anil) (amguᵛ-spec (suc k) p rg A B)
             (λ u → box-inj u)

  amguᵛ-spec zero p rg (tvar α) (tvar β) anil = flexFlexᵗ-spec rg α β
  amguᵛ-spec zero p rg (tvar α) (Base b') anil = flexᵗ-spec rg α (Base b') (λ ())
  amguᵛ-spec zero p rg (tvar α) Unit anil = flexᵗ-spec rg α Unit (λ ())
  amguᵛ-spec zero p rg (tvar α) Bool anil = flexᵗ-spec rg α Bool (λ ())
  amguᵛ-spec zero p rg (tvar α) (B |×| B') anil = flexᵗ-spec rg α (B |×| B') (λ ())
  amguᵛ-spec zero p rg (tvar α) Empty anil = flexᵗ-spec rg α Empty (λ ())
  amguᵛ-spec zero p rg (tvar α) (B ⇒ D) anil = flexᵗ-spec rg α (B ⇒ D) (λ ())
  amguᵛ-spec zero p rg (tvar α) ([ ρ' ] B) anil = flexᵗ-spec rg α ([ ρ' ] B) (λ ())
  amguᵛ-spec zero p rg (Base b) (tvar β) anil = Spec-map sym (flexᵗ-spec rg β (Base b) (λ ()))
  amguᵛ-spec zero p rg Unit (tvar β) anil = Spec-map sym (flexᵗ-spec rg β Unit (λ ()))
  amguᵛ-spec zero p rg Bool (tvar β) anil = Spec-map sym (flexᵗ-spec rg β Bool (λ ()))
  amguᵛ-spec zero p rg (A |×| A') (tvar β) anil = Spec-map sym (flexᵗ-spec rg β (A |×| A') (λ ()))
  amguᵛ-spec zero p rg Empty (tvar β) anil = Spec-map sym (flexᵗ-spec rg β Empty (λ ()))
  amguᵛ-spec zero p rg (A ⇒ C) (tvar β) anil = Spec-map sym (flexᵗ-spec rg β (A ⇒ C) (λ ()))
  amguᵛ-spec zero p rg ([ ρ ] A) (tvar β) anil = Spec-map sym (flexᵗ-spec rg β ([ ρ ] A) (λ ()))
  amguᵛ-spec zero p rg (Base b) (Base b') anil = const-spec (b ≡ᵇ? b') (λ δ u → Base-inj u)
  amguᵛ-spec zero p rg Unit Unit anil = keep
  amguᵛ-spec zero p rg Bool Bool anil = keep
  amguᵛ-spec zero p rg Empty Empty anil = keep
  amguᵛ-spec {Θ} zero p rg (A |×| A') (B |×| B') anil =
    seq-spec (amguᵛ zero p rg A B (Θ , anil)) (amguᵛ zero p rg A' B')
             (amguᵛ-spec zero p rg A B anil) (amguᵛ-spec zero p rg A' B')
             (λ u → ×-inj u)
  amguᵛ-spec {Θ} zero p rg (A ⇒ C) (B ⇒ D) anil =
    seq-spec (amguᵛ zero p rg A B (Θ , anil)) (amguᶜ zero p rg C D)
             (amguᵛ-spec zero p rg A B anil) (amguᶜ-spec zero p rg C D)
             (λ u → ⇒-inj u)
  amguᵛ-spec {Θ} zero p rg ([ ρ ] A) ([ ρ' ] B) anil =
    seq-spec (amguʳ zero p rg ρ ρ' (Θ , anil)) (amguᵛ zero p rg A B)
             (amguʳ-spec zero p rg ρ ρ' anil) (amguᵛ-spec zero p rg A B)
             (λ u → box-inj u)

  -- head mismatches: no substitution unifies the two sides

  amguᵛ-spec k p rg (Base b) Unit anil = clash (λ δ ())
  amguᵛ-spec k p rg (Base b) Bool anil = clash (λ δ ())
  amguᵛ-spec k p rg (Base b) (B |×| B') anil = clash (λ δ ())
  amguᵛ-spec k p rg (Base b) Empty anil = clash (λ δ ())
  amguᵛ-spec k p rg (Base b) (B ⇒ D) anil = clash (λ δ ())
  amguᵛ-spec k p rg (Base b) ([ ρ' ] B) anil = clash (λ δ ())
  amguᵛ-spec k p rg Unit (Base b') anil = clash (λ δ ())
  amguᵛ-spec k p rg Unit Bool anil = clash (λ δ ())
  amguᵛ-spec k p rg Unit (B |×| B') anil = clash (λ δ ())
  amguᵛ-spec k p rg Unit Empty anil = clash (λ δ ())
  amguᵛ-spec k p rg Unit (B ⇒ D) anil = clash (λ δ ())
  amguᵛ-spec k p rg Unit ([ ρ' ] B) anil = clash (λ δ ())
  amguᵛ-spec k p rg Bool (Base b') anil = clash (λ δ ())
  amguᵛ-spec k p rg Bool Unit anil = clash (λ δ ())
  amguᵛ-spec k p rg Bool (B |×| B') anil = clash (λ δ ())
  amguᵛ-spec k p rg Bool Empty anil = clash (λ δ ())
  amguᵛ-spec k p rg Bool (B ⇒ D) anil = clash (λ δ ())
  amguᵛ-spec k p rg Bool ([ ρ' ] B) anil = clash (λ δ ())
  amguᵛ-spec k p rg (A |×| A') (Base b') anil = clash (λ δ ())
  amguᵛ-spec k p rg (A |×| A') Unit anil = clash (λ δ ())
  amguᵛ-spec k p rg (A |×| A') Bool anil = clash (λ δ ())
  amguᵛ-spec k p rg (A |×| A') Empty anil = clash (λ δ ())
  amguᵛ-spec k p rg (A |×| A') (B ⇒ D) anil = clash (λ δ ())
  amguᵛ-spec k p rg (A |×| A') ([ ρ' ] B) anil = clash (λ δ ())
  amguᵛ-spec k p rg Empty (Base b') anil = clash (λ δ ())
  amguᵛ-spec k p rg Empty Unit anil = clash (λ δ ())
  amguᵛ-spec k p rg Empty Bool anil = clash (λ δ ())
  amguᵛ-spec k p rg Empty (B |×| B') anil = clash (λ δ ())
  amguᵛ-spec k p rg Empty (B ⇒ D) anil = clash (λ δ ())
  amguᵛ-spec k p rg Empty ([ ρ' ] B) anil = clash (λ δ ())
  amguᵛ-spec k p rg (A ⇒ C) (Base b') anil = clash (λ δ ())
  amguᵛ-spec k p rg (A ⇒ C) Unit anil = clash (λ δ ())
  amguᵛ-spec k p rg (A ⇒ C) Bool anil = clash (λ δ ())
  amguᵛ-spec k p rg (A ⇒ C) (B |×| B') anil = clash (λ δ ())
  amguᵛ-spec k p rg (A ⇒ C) Empty anil = clash (λ δ ())
  amguᵛ-spec k p rg (A ⇒ C) ([ ρ' ] B) anil = clash (λ δ ())
  amguᵛ-spec k p rg ([ ρ ] A) (Base b') anil = clash (λ δ ())
  amguᵛ-spec k p rg ([ ρ ] A) Unit anil = clash (λ δ ())
  amguᵛ-spec k p rg ([ ρ ] A) Bool anil = clash (λ δ ())
  amguᵛ-spec k p rg ([ ρ ] A) (B |×| B') anil = clash (λ δ ())
  amguᵛ-spec k p rg ([ ρ ] A) Empty anil = clash (λ δ ())
  amguᵛ-spec k p rg ([ ρ ] A) (B ⇒ D) anil = clash (λ δ ())

  -- computation types

  amguᶜ-spec (suc k) p rg C D (X /ᵗ α ∷ τ) =
    descᵗ-spec X α rg (eqᶜ C D) τ
      (amguᶜ-spec k (szᵗ τ p) rg (C [ X forᵗ α ]ᶜ) (D [ X forᵗ α ]ᶜ) τ)
  amguᶜ-spec (suc k) p rg C D (X /ʳ i ∷ τ) =
    descʳ-spec X i rg (eqᶜ C D) τ
      (amguᶜ-spec k (szʳ τ p) rg (C [ X forʳ i ]ᶜ) (D [ X forʳ i ]ᶜ) τ)
  amguᶜ-spec (suc k) p rg C D (X /ᵉ i ∷ τ) =
    descᵉ-spec X i rg (eqᶜ C D) τ
      (amguᶜ-spec k (szᵉ τ p) (popʳᵍ τ i rg) (C [ X forᵉ i ]ᶜ) (D [ X forᵉ i ]ᶜ) τ)
  amguᶜ-spec zero p rg C D (X /ᵗ α ∷ τ) = sz0ᵗ τ p
  amguᶜ-spec zero p rg C D (X /ʳ i ∷ τ) = sz0ʳ τ p
  amguᶜ-spec zero p rg C D (X /ᵉ i ∷ τ) = sz0ᵉ τ p
  amguᶜ-spec {Θ} (suc k) p rg (A ‼ ε) (B ‼ ε') anil =
    seq-spec (amguᵛ (suc k) p rg A B (Θ , anil)) (amguᵉ (suc k) p rg ε ε')
             (amguᵛ-spec (suc k) p rg A B anil) (amguᵉ-spec (suc k) p rg ε ε')
             (λ u → ‼-inj u)
  amguᶜ-spec {Θ} zero p rg (A ‼ ε) (B ‼ ε') anil =
    seq-spec (amguᵛ zero p rg A B (Θ , anil)) (amguᵉ zero p rg ε ε')
             (amguᵛ-spec zero p rg A B anil) (amguᵉ-spec zero p rg ε ε')
             (λ u → ‼-inj u)

  -- resource grades

  amguʳ-spec (suc k) p rg ρ₀ ρ₁ (X /ᵗ α ∷ τ) =
    descᵗ-spec X α rg (eqʳ ρ₀ ρ₁) τ
      (amguʳ-spec k (szᵗ τ p) rg (ρ₀ [ X forᵗ α ]ʳ) (ρ₁ [ X forᵗ α ]ʳ) τ)
  amguʳ-spec (suc k) p rg ρ₀ ρ₁ (X /ʳ i ∷ τ) =
    descʳ-spec X i rg (eqʳ ρ₀ ρ₁) τ
      (amguʳ-spec k (szʳ τ p) rg (ρ₀ [ X forʳ i ]ʳ) (ρ₁ [ X forʳ i ]ʳ) τ)
  amguʳ-spec (suc k) p rg ρ₀ ρ₁ (X /ᵉ i ∷ τ) =
    descᵉ-spec X i rg (eqʳ ρ₀ ρ₁) τ
      (amguʳ-spec k (szᵉ τ p) (popʳᵍ τ i rg) (ρ₀ [ X forᵉ i ]ʳ) (ρ₁ [ X forᵉ i ]ʳ) τ)
  amguʳ-spec zero p rg ρ₀ ρ₁ (X /ᵗ α ∷ τ) = sz0ᵗ τ p
  amguʳ-spec zero p rg ρ₀ ρ₁ (X /ʳ i ∷ τ) = sz0ʳ τ p
  amguʳ-spec zero p rg ρ₀ ρ₁ (X /ᵉ i ∷ τ) = sz0ᵉ τ p
  amguʳ-spec (suc k) p rg (rvar i) (rvar j) anil = flexFlexʳ-spec rg i j
  amguʳ-spec (suc k) p rg (rvar i) (rconst d) anil = flexʳ-spec rg i (rconst d) (λ ())
  amguʳ-spec (suc k) p rg (rvar i) (ρ₁' ·̂ᵣ ρ₂') anil = flexʳ-spec rg i (ρ₁' ·̂ᵣ ρ₂') (λ ())
  amguʳ-spec (suc k) p rg (rvar i) ∣ ε' ∣̂ᵉ anil = flexʳ-spec rg i ∣ ε' ∣̂ᵉ (λ ())
  amguʳ-spec (suc k) p rg (rconst c) (rvar j) anil = Spec-map sym (flexʳ-spec rg j (rconst c) (λ ()))
  amguʳ-spec (suc k) p rg (ρ₁ ·̂ᵣ ρ₂) (rvar j) anil = Spec-map sym (flexʳ-spec rg j (ρ₁ ·̂ᵣ ρ₂) (λ ()))
  amguʳ-spec (suc k) p rg ∣ ε ∣̂ᵉ (rvar j) anil = Spec-map sym (flexʳ-spec rg j ∣ ε ∣̂ᵉ (λ ()))
  amguʳ-spec (suc k) p rg (rconst c) (rconst d) anil = const-spec (c ≡ᵣ? d) (λ δ u → rconst-inj u)
  amguʳ-spec {Θ} (suc k) p rg (ρ₁ ·̂ᵣ ρ₂) (ρ₁' ·̂ᵣ ρ₂') anil =
    seq-spec (amguʳ (suc k) p rg ρ₁ ρ₁' (Θ , anil)) (amguʳ (suc k) p rg ρ₂ ρ₂')
             (amguʳ-spec (suc k) p rg ρ₁ ρ₁' anil) (amguʳ-spec (suc k) p rg ρ₂ ρ₂')
             (λ u → ·ᵣ-inj u)
  amguʳ-spec (suc k) p rg ∣ ε ∣̂ᵉ ∣ ε' ∣̂ᵉ anil =
    Spec-map (λ u → ∣∣-inj u) (amguᵉ-spec (suc k) p rg ε ε' anil)

  amguʳ-spec zero p rg (rvar i) (rvar j) anil = flexFlexʳ-spec rg i j
  amguʳ-spec zero p rg (rvar i) (rconst d) anil = flexʳ-spec rg i (rconst d) (λ ())
  amguʳ-spec zero p rg (rvar i) (ρ₁' ·̂ᵣ ρ₂') anil = flexʳ-spec rg i (ρ₁' ·̂ᵣ ρ₂') (λ ())
  amguʳ-spec zero p rg (rvar i) ∣ ε' ∣̂ᵉ anil = flexʳ-spec rg i ∣ ε' ∣̂ᵉ (λ ())
  amguʳ-spec zero p rg (rconst c) (rvar j) anil = Spec-map sym (flexʳ-spec rg j (rconst c) (λ ()))
  amguʳ-spec zero p rg (ρ₁ ·̂ᵣ ρ₂) (rvar j) anil = Spec-map sym (flexʳ-spec rg j (ρ₁ ·̂ᵣ ρ₂) (λ ()))
  amguʳ-spec zero p rg ∣ ε ∣̂ᵉ (rvar j) anil = Spec-map sym (flexʳ-spec rg j ∣ ε ∣̂ᵉ (λ ()))
  amguʳ-spec zero p rg (rconst c) (rconst d) anil = const-spec (c ≡ᵣ? d) (λ δ u → rconst-inj u)
  amguʳ-spec {Θ} zero p rg (ρ₁ ·̂ᵣ ρ₂) (ρ₁' ·̂ᵣ ρ₂') anil =
    seq-spec (amguʳ zero p rg ρ₁ ρ₁' (Θ , anil)) (amguʳ zero p rg ρ₂ ρ₂')
             (amguʳ-spec zero p rg ρ₁ ρ₁' anil) (amguʳ-spec zero p rg ρ₂ ρ₂')
             (λ u → ·ᵣ-inj u)
  amguʳ-spec zero p rg ∣ ε ∣̂ᵉ ∣ ε' ∣̂ᵉ anil =
    Spec-map (λ u → ∣∣-inj u) (amguᵉ-spec zero p rg ε ε' anil)

  -- head mismatches, including a grade image against a resource former

  amguʳ-spec k p rg (rconst c) (ρ₁' ·̂ᵣ ρ₂') anil = clash (λ δ ())
  amguʳ-spec k p rg (rconst c) ∣ ε' ∣̂ᵉ anil = clash (λ δ ())
  amguʳ-spec k p rg (ρ₁ ·̂ᵣ ρ₂) (rconst d) anil = clash (λ δ ())
  amguʳ-spec k p rg (ρ₁ ·̂ᵣ ρ₂) ∣ ε' ∣̂ᵉ anil = clash (λ δ ())
  amguʳ-spec k p rg ∣ ε ∣̂ᵉ (rconst d) anil = clash (λ δ ())
  amguʳ-spec k p rg ∣ ε ∣̂ᵉ (ρ₁' ·̂ᵣ ρ₂') anil = clash (λ δ ())

  -- effect grades

  amguᵉ-spec (suc k) p rg ε ε' (X /ᵗ α ∷ τ) =
    descᵗ-spec X α rg (eqᵉ ε ε') τ
      (amguᵉ-spec k (szᵗ τ p) rg (ε [ X forᵗ α ]ᵉ) (ε' [ X forᵗ α ]ᵉ) τ)
  amguᵉ-spec (suc k) p rg ε ε' (X /ʳ i ∷ τ) =
    descʳ-spec X i rg (eqᵉ ε ε') τ
      (amguᵉ-spec k (szʳ τ p) rg (ε [ X forʳ i ]ᵉ) (ε' [ X forʳ i ]ᵉ) τ)
  amguᵉ-spec (suc k) p rg ε ε' (X /ᵉ i ∷ τ) =
    descᵉ-spec X i rg (eqᵉ ε ε') τ
      (amguᵉ-spec k (szᵉ τ p) (popʳᵍ τ i rg) (ε [ X forᵉ i ]ᵉ) (ε' [ X forᵉ i ]ᵉ) τ)
  amguᵉ-spec zero p rg ε ε' (X /ᵗ α ∷ τ) = sz0ᵗ τ p
  amguᵉ-spec zero p rg ε ε' (X /ʳ i ∷ τ) = sz0ʳ τ p
  amguᵉ-spec zero p rg ε ε' (X /ᵉ i ∷ τ) = sz0ᵉ τ p
  amguᵉ-spec (suc k) p rg (evar i) (evar j) anil = flexFlexᵉ-spec rg i j
  amguᵉ-spec (suc k) p rg (evar i) (econst d) anil = flexᵉ-spec rg i (econst d) (nvconstᵉ d)
  amguᵉ-spec (suc k) p rg (evar i) (ε₁' ·̂ₑ ε₂') anil = flexᵉ-spec rg i (ε₁' ·̂ₑ ε₂') (nvmulᵉ ε₁' ε₂')
  amguᵉ-spec (suc k) p rg (econst c) (evar j) anil = Spec-map sym (flexᵉ-spec rg j (econst c) (nvconstᵉ c))
  amguᵉ-spec (suc k) p rg (ε₁ ·̂ₑ ε₂) (evar j) anil = Spec-map sym (flexᵉ-spec rg j (ε₁ ·̂ₑ ε₂) (nvmulᵉ ε₁ ε₂))
  amguᵉ-spec (suc k) p rg (econst c) (econst d) anil = const-spec (c ≡ₑ? d) (λ δ u → econst-inj u)
  amguᵉ-spec {Θ} (suc k) p rg (ε₁ ·̂ₑ ε₂) (ε₁' ·̂ₑ ε₂') anil =
    seq-spec (amguᵉ (suc k) p rg ε₁ ε₁' (Θ , anil)) (amguᵉ (suc k) p rg ε₂ ε₂')
             (amguᵉ-spec (suc k) p rg ε₁ ε₁' anil) (amguᵉ-spec (suc k) p rg ε₂ ε₂')
             (λ u → ·ₑ-inj u)

  amguᵉ-spec zero p rg (evar i) (evar j) anil = flexFlexᵉ-spec rg i j
  amguᵉ-spec zero p rg (evar i) (econst d) anil = flexᵉ-spec rg i (econst d) (nvconstᵉ d)
  amguᵉ-spec zero p rg (evar i) (ε₁' ·̂ₑ ε₂') anil = flexᵉ-spec rg i (ε₁' ·̂ₑ ε₂') (nvmulᵉ ε₁' ε₂')
  amguᵉ-spec zero p rg (econst c) (evar j) anil = Spec-map sym (flexᵉ-spec rg j (econst c) (nvconstᵉ c))
  amguᵉ-spec zero p rg (ε₁ ·̂ₑ ε₂) (evar j) anil = Spec-map sym (flexᵉ-spec rg j (ε₁ ·̂ₑ ε₂) (nvmulᵉ ε₁ ε₂))
  amguᵉ-spec zero p rg (econst c) (econst d) anil = const-spec (c ≡ₑ? d) (λ δ u → econst-inj u)
  amguᵉ-spec {Θ} zero p rg (ε₁ ·̂ₑ ε₂) (ε₁' ·̂ₑ ε₂') anil =
    seq-spec (amguᵉ zero p rg ε₁ ε₁' (Θ , anil)) (amguᵉ zero p rg ε₂ ε₂')
             (amguᵉ-spec zero p rg ε₁ ε₁' anil) (amguᵉ-spec zero p rg ε₂ ε₂')
             (λ u → ·ₑ-inj u)

  amguᵉ-spec k p rg (econst c) (ε₁' ·̂ₑ ε₂') anil = clash (λ δ ())
  amguᵉ-spec k p rg (ε₁ ·̂ₑ ε₂) (econst d) anil = clash (λ δ ())

--------------------------------------------------------------
-- Solving a list of equations                               --
--------------------------------------------------------------

amguᴱ-spec : ∀ {Θ Θ'} → (rg : Rig Θ) → (e : Eqn Θ) → (ρ : AList Θ Θ')
           → Spec rg (Uni e) ρ (amguᴱ rg e (Θ' , ρ))
amguᴱ-spec {Θ} rg (eqᵛ A B)  ρ = amguᵛ-spec (Sz Θ) refl rg A B ρ
amguᴱ-spec {Θ} rg (eqᶜ C D)  ρ = amguᶜ-spec (Sz Θ) refl rg C D ρ
amguᴱ-spec {Θ} rg (eqʳ ρ₀ ρ₁) ρ = amguʳ-spec (Sz Θ) refl rg ρ₀ ρ₁ ρ
amguᴱ-spec {Θ} rg (eqᵉ ε ε')  ρ = amguᵉ-spec (Sz Θ) refl rg ε ε' ρ

unifyᴬ-spec : ∀ {Θ Θ'} → (rg : Rig Θ) → (es : Eqns Θ) → (ρ : AList Θ Θ')
            → Spec rg (Unis es) ρ (unifyᴬ rg es (Θ' , ρ))
unifyᴬ-spec rg []           ρ = keep
unifyᴬ-spec {Θ} {Θ'} rg (e ∷ es) ρ =
  seq-spec (amguᴱ rg e (Θ' , ρ)) (unifyᴬ rg es)
           (amguᴱ-spec rg e ρ) (λ ρ₁ → unifyᴬ-spec rg es ρ₁)
           (λ u → u)

--------------------------------------------------------------
-- Most general unifier, and refutation                      --
--------------------------------------------------------------

-- Maximality does not need the rigid hypothesis: a store never
-- binds a rigid variable, so every unifier factors through it.

unify-max : ∀ {Θ Θ⁺} → (rg : Rig Θ) → (es : Eqns Θ) → {ρ : AList Θ Θ⁺}
          → unify rg es ≡ just (Θ⁺ , ρ)
          → ∀ {Θ''} → (σ : Subst Θ Θ'') → Unifies es σ
          → Σ[ δ ∈ Subst Θ⁺ Θ'' ] ((⟦ ρ ⟧ᴬ ⨟ˢ δ) ≐ˢ σ)
unify-max rg es eq σ u = fact (onJust (unifyᴬ-spec rg es anil) eq) σ u

unify-mgu : ∀ {Θ Θ⁺} → (rg : Rig Θ) → (es : Eqns Θ) → {ρ : AList Θ Θ⁺}
          → unify rg es ≡ just (Θ⁺ , ρ)
          → ∀ {Θ''} → (σ : Subst Θ Θ'') → Fixing rg σ → Unifies es σ
          → Σ[ δ ∈ Subst Θ⁺ Θ'' ] ((⟦ ρ ⟧ᴬ ⨟ˢ δ) ≐ˢ σ)
unify-mgu rg es eq σ fx u = unify-max rg es eq σ u

unify-fail : ∀ {Θ} → (rg : Rig Θ) → (es : Eqns Θ) → unify rg es ≡ nothing
           → ∀ {Θ''} → (σ : Subst Θ Θ'') → Fixing rg σ → ¬ Unifies es σ
unify-fail rg es eq σ fx u = onNothing (unifyᴬ-spec rg es anil) eq σ fx u

--------------------------------------------------------------
-- Sanity checks                                             --
--------------------------------------------------------------

private

  -- one type variable, bound to a product by the only equation

  Θ₁ : Scope
  Θ₁ = ∅ˢ +ty

  es₁ : Eqns Θ₁
  es₁ = eqᵛ (tvar (newᵗ {∅ˢ})) (Unit |×| Unit) ∷ []

  -- a solution of its own, which the store must dominate

  σ₁ : Subst Θ₁ ∅ˢ
  σ₁ = sub (λ α → Unit |×| Unit) (λ ()) (λ ())

  fx₁ : Fixing [] σ₁
  fx₁ = fixing (λ ()) (λ ())

  ex-mgu : Σ[ δ ∈ Subst ∅ˢ ∅ˢ ]
             ((⟦ (Unit |×| Unit) /ᵗ newᵗ {∅ˢ} ∷ anil ⟧ᴬ ⨟ˢ δ) ≐ˢ σ₁)
  ex-mgu = unify-mgu [] es₁ refl σ₁ fx₁ (refl , tt)

  -- two type variables, one bound to the other: a solution that sends
  -- both to `Unit` factors through the binding

  Θ₂ : Scope
  Θ₂ = ∅ˢ +ty +ty

  es₂ : Eqns Θ₂
  es₂ = eqᵛ (tvar (newᵗ {∅ˢ +ty})) (tvar (wkᵗ-tv (∅ˢ +ty) (newᵗ {∅ˢ}))) ∷ []

  σ₂ : Subst Θ₂ ∅ˢ
  σ₂ = sub (λ α → Unit) (λ ()) (λ ())

  ex-mgu-var : Σ[ δ ∈ Subst (∅ˢ +ty) ∅ˢ ]
                 ((⟦ tvar (newᵗ {∅ˢ}) /ᵗ newᵗ {∅ˢ +ty} ∷ anil ⟧ᴬ ⨟ˢ δ) ≐ˢ σ₂)
  ex-mgu-var = unify-mgu [] es₂ refl σ₂ (fixing (λ ()) (λ ())) (refl , tt)

  -- a clash refutes its equation for every substitution

  es₃ : Eqns ∅ˢ
  es₃ = eqᵛ Unit Bool ∷ []

  ex-clash : ∀ {Θ''} → (σ : Subst ∅ˢ Θ'') → Fixing [] σ → ¬ Unifies es₃ σ
  ex-clash = unify-fail [] es₃ refl

  -- a rigid variable is refuted by its image being a variable

  Θ₄ : Scope
  Θ₄ = ∅ˢ +e

  es₄ : Eqns Θ₄
  es₄ = eqᵉ (evar (newᵉ {∅ˢ})) ûₑ ∷ []

  ex-rigid : ∀ {Θ''} → (σ : Subst Θ₄ Θ'') → Fixing (newᵉ {∅ˢ} ∷ []) σ → ¬ Unifies es₄ σ
  ex-rigid = unify-fail (newᵉ {∅ˢ} ∷ []) es₄ refl

  -- and the identity is such a substitution

  ex-rigid-id : ¬ Unifies es₄ (idˢ {Θ₄})
  ex-rigid-id = ex-rigid idˢ (Fixing-id (newᵉ {∅ˢ} ∷ []))
