------------------------------------------------------------------
-- Type formers and the variance of their parts                 --
--                                                              --
-- An open type other than a type variable is a former applied  --
-- to its parts: value types, the grade of a box and the effect --
-- of a function type. `Decomp A B ps` is the variance table:   --
-- `A` and `B` have one former, and `ps` pairs their parts,     --
-- left to right, each with its variance (`co`, `contra`,       --
-- `inv`) and its sort (`ty`, `rg`, `eg`). `decompose` decides  --
-- it on two types, `self` reads it off one type, and           --
-- `eternal` is the eternality column: a former is never        --
-- eternal, or eternal exactly when its value-type parts are.   --
--                                                              --
-- The table is exact at every pair of instances: `A [ σ ]` is  --
-- a subtype of `B [ τ ]` exactly when every pair of parts      --
-- holds at its variance (`<:-intro`, `<:-elim`), and `A [ δ ]` --
-- is eternal exactly when the column admits the former and     --
-- every value-type part is eternal (`⊩ᴱ-intro`, `⊩ᴱ-elim`).    --
-- The value-type parts of a type are smaller than it (`_≺_`,   --
-- `≺-wf`), so recursion along the table is well founded.       --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.Empty.Irrelevant using () renaming (⊥-elim to ⊥-elim-irr)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Former (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (_≡ᵇ?_; eternalBaseType?)

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S

-- How the parts at one position of two types of one former are
-- related by a subtyping demand between the two

data Variance : Set where
  co contra inv : Variance

-- A demand and its converse, at a variance

Var : Variance → Set → Set → Set
Var co     P P' = P
Var contra P P' = P'
Var inv    P P' = P × P'

At : ∀ {X : Set} → Variance → (X → X → Set) → X → X → Set
At v R x y = Var v (R x y) (R y x)

-- A pair of parts at one position, with its variance and sort

data Part (Ψ : Scope) : Set where
  ty : Variance → OVType Ψ → OVType Ψ → Part Ψ    -- value types
  rg : Variance → RExp Ψ → RExp Ψ → Part Ψ        -- resource grades
  eg : Variance → EExp Ψ → EExp Ψ → Part Ψ        -- effect grades

infixl 50 _[_∣_]ᴾ

_[_∣_]ᴾ : ∀ {Ψ Ψ'} → Part Ψ → Subst Ψ Ψ' → Subst Ψ Ψ' → Part Ψ'
ty v A B [ σ ∣ τ ]ᴾ = ty v (A [ σ ]ᵛ) (B [ τ ]ᵛ)
rg v ρ ρ' [ σ ∣ τ ]ᴾ = rg v (ρ [ σ ]ʳ) (ρ' [ τ ]ʳ)
eg v ε ε' [ σ ∣ τ ]ᴾ = eg v (ε [ σ ]ᵉ) (ε' [ τ ]ᵉ)

-- The demand a pair of parts makes, at its variance

Holdsᴾ : ∀ {Ψ} → Hyps Ψ → Part Ψ → Set
Holdsᴾ Q (ty v A B)  = At v (Q ∣_<:̂ᵛ_) A B
Holdsᴾ Q (rg v ρ ρ') = At v (Q ⊩_≾̂ᵣ_) ρ ρ'
Holdsᴾ Q (eg v ε ε') = At v (Q ⊩_≾̂ₑ_) ε ε'

-- The variance table

data Decomp {Ψ : Scope} : OVType Ψ → OVType Ψ → List (Part Ψ) → Set where
  Baseᴰ  : ∀ {b} → Decomp (Base b) (Base b) []
  Unitᴰ  : Decomp Unit Unit []
  Boolᴰ  : Decomp Bool Bool []
  Natᴰ   : Decomp Nat Nat []
  Emptyᴰ : Decomp Empty Empty []
  |×|ᴰ   : ∀ {A A' B B'}
         → Decomp (A |×| B) (A' |×| B') (ty co A A' ∷ ty co B B' ∷ [])
  |+|ᴰ   : ∀ {A A' B B'}
         → Decomp (A |+| B) (A' |+| B') (ty co A A' ∷ ty co B B' ∷ [])
  |List|ᴰ : ∀ {A A'}
          → Decomp (|List| A) (|List| A') (ty co A A' ∷ [])
  ⇒ᴰ     : ∀ {A A' B B' ε ε'}
         → Decomp (A ⇒ B ‼ ε) (A' ⇒ B' ‼ ε')
                  (ty contra A A' ∷ ty co B B' ∷ eg co ε ε' ∷ [])
  []ᴰ    : ∀ {ρ ρ' A A'}
         → Decomp ([ ρ ] A) ([ ρ' ] A') (rg contra ρ ρ' ∷ ty co A A' ∷ [])

-- Two types: a pair of type variables, one former, or a clash

data Shape {Ψ : Scope} : OVType Ψ → OVType Ψ → Set where
  vars  : (α β : TyVar Ψ) → Shape (tvar α) (tvar β)
  parts : ∀ {A B} → (ps : List (Part Ψ)) → Decomp A B ps → Shape A B
  clash : ∀ {A B} → Shape A B

decompose : ∀ {Ψ} → (A B : OVType Ψ) → Shape A B
decompose (tvar α)       (tvar β)          = vars α β
decompose (Base b)       (Base b')         with b ≡ᵇ? b'
... | yes refl = parts _ Baseᴰ
... | no _     = clash
decompose Unit           Unit              = parts _ Unitᴰ
decompose Bool           Bool              = parts _ Boolᴰ
decompose Nat            Nat               = parts _ Natᴰ
decompose Empty          Empty             = parts _ Emptyᴰ
decompose (A |×| B)      (A' |×| B')       = parts _ |×|ᴰ
decompose (A |+| B)      (A' |+| B')       = parts _ |+|ᴰ
decompose (|List| A)     (|List| A')       = parts _ |List|ᴰ
decompose (A ⇒ (B ‼ ε))  (A' ⇒ (B' ‼ ε'))  = parts _ ⇒ᴰ
decompose ([ ρ ] A)      ([ ρ' ] A')       = parts _ []ᴰ
decompose _              _                 = clash

-- One type: a type variable, or its former against itself, whose
-- pairs of parts are diagonal

Diag : ∀ {Ψ} → Part Ψ → Set
Diag (ty _ A B)  = A ≡ B
Diag (rg _ ρ ρ') = ρ ≡ ρ'
Diag (eg _ ε ε') = ε ≡ ε'

data Self {Ψ : Scope} : OVType Ψ → Set where
  var  : (α : TyVar Ψ) → Self (tvar α)
  form : ∀ {A} → (ps : List (Part Ψ)) → Decomp A A ps → All Diag ps → Self A

self : ∀ {Ψ} → (A : OVType Ψ) → Self A
self (tvar α)      = var α
self (Base b)      = form _ Baseᴰ []
self Unit          = form _ Unitᴰ []
self Bool          = form _ Boolᴰ []
self Nat           = form _ Natᴰ []
self Empty         = form _ Emptyᴰ []
self (A |×| B)     = form _ |×|ᴰ (refl ∷ refl ∷ [])
self (A |+| B)     = form _ |+|ᴰ (refl ∷ refl ∷ [])
self (|List| A)    = form _ |List|ᴰ (refl ∷ [])
self (A ⇒ (B ‼ ε)) = form _ ⇒ᴰ (refl ∷ refl ∷ refl ∷ [])
self ([ ρ ] A)     = form _ []ᴰ (refl ∷ refl ∷ [])

-- The eternality column

eternal : ∀ {Ψ} {A B : OVType Ψ} {ps} → Decomp A B ps → 𝔹
eternal (Baseᴰ {b}) = ⌊ eternalBaseType? b ⌋
eternal Unitᴰ       = true
eternal Boolᴰ       = true
eternal Natᴰ        = true
eternal Emptyᴰ      = true
eternal |×|ᴰ        = true
eternal |+|ᴰ        = true
eternal |List|ᴰ     = true
eternal ⇒ᴰ          = false
eternal []ᴰ         = false

-- The table is exact for subtyping, at every pair of instances

<:-intro : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {A B : OVType Ψ} {ps} → Decomp A B ps
         → (σ τ : Subst Ψ Ψ') → All (λ p → Holdsᴾ Q (p [ σ ∣ τ ]ᴾ)) ps
         → Q ∣ A [ σ ]ᵛ <:̂ᵛ B [ τ ]ᵛ
<:-intro Baseᴰ  σ τ []              = Baseₛ refl
<:-intro Unitᴰ  σ τ []              = Unitₛ
<:-intro Boolᴰ  σ τ []              = Boolₛ
<:-intro Natᴰ   σ τ []              = Natₛ
<:-intro Emptyᴰ σ τ []              = Emptyₛ
<:-intro |×|ᴰ   σ τ (p ∷ q ∷ [])     = p |×|ₛ q
<:-intro |+|ᴰ   σ τ (p ∷ q ∷ [])     = p |+|ₛ q
<:-intro |List|ᴰ σ τ (p ∷ [])        = |List|ₛ p
<:-intro ⇒ᴰ     σ τ (p ∷ q ∷ e ∷ []) = p ⇒ₛ (q ‼ₛ e)
<:-intro []ᴰ    σ τ (r ∷ p ∷ [])     = [ r ]ₛ p

<:-elim : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {A B : OVType Ψ} {ps} → Decomp A B ps
        → (σ τ : Subst Ψ Ψ') → Q ∣ A [ σ ]ᵛ <:̂ᵛ B [ τ ]ᵛ
        → All (λ p → Holdsᴾ Q (p [ σ ∣ τ ]ᴾ)) ps
<:-elim Baseᴰ  σ τ (Baseₛ _)        = []
<:-elim Unitᴰ  σ τ Unitₛ            = []
<:-elim Boolᴰ  σ τ Boolₛ            = []
<:-elim Natᴰ   σ τ Natₛ             = []
<:-elim Emptyᴰ σ τ Emptyₛ           = []
<:-elim |×|ᴰ   σ τ (p |×|ₛ q)       = p ∷ q ∷ []
<:-elim |+|ᴰ   σ τ (p |+|ₛ q)       = p ∷ q ∷ []
<:-elim |List|ᴰ σ τ (|List|ₛ p)      = p ∷ []
<:-elim ⇒ᴰ     σ τ (p ⇒ₛ (q ‼ₛ e))  = p ∷ q ∷ e ∷ []
<:-elim []ᴰ    σ τ ([ r ]ₛ p)       = r ∷ p ∷ []

-- The table is exact for eternality, at every instance; a grade part
-- demands nothing

Etᴾ : ∀ {Ψ} → Hyps Ψ → Part Ψ → Set
Etᴾ Q (ty _ A _) = Q ⊩ᴱ A
Etᴾ Q (rg _ _ _) = ⊤
Etᴾ Q (eg _ _ _) = ⊤

⊩ᴱ-intro : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {A B : OVType Ψ} {ps} → (g : Decomp A B ps)
         → eternal g ≡ true → (δ : Subst Ψ Ψ')
         → All (λ p → Etᴾ Q (p [ δ ∣ δ ]ᴾ)) ps → Q ⊩ᴱ A [ δ ]ᵛ
⊩ᴱ-intro (Baseᴰ {b}) e δ [] with eternalBaseType? b
... | yes p = Baseₑ p
⊩ᴱ-intro (Baseᴰ {b}) () δ [] | no _
⊩ᴱ-intro Unitᴰ  e  δ []           = Unitₑ
⊩ᴱ-intro Boolᴰ  e  δ []           = Boolₑ
⊩ᴱ-intro Natᴰ   e  δ []           = Natₑ
⊩ᴱ-intro Emptyᴰ e  δ []           = Emptyₑ
⊩ᴱ-intro |×|ᴰ   e  δ (p ∷ q ∷ []) = p |×|ₑ q
⊩ᴱ-intro |+|ᴰ   e  δ (p ∷ q ∷ []) = p |+|ₑ q
⊩ᴱ-intro |List|ᴰ e δ (p ∷ [])     = |List|ₑ p

⊩ᴱ-elim : ∀ {Ψ Ψ'} {Q : Hyps Ψ'} {A B : OVType Ψ} {ps} → (g : Decomp A B ps)
        → (δ : Subst Ψ Ψ') → Q ⊩ᴱ A [ δ ]ᵛ
        → (eternal g ≡ true) × All (λ p → Etᴾ Q (p [ δ ∣ δ ]ᴾ)) ps
⊩ᴱ-elim (Baseᴰ {b}) δ (Baseₑ p) with eternalBaseType? b
... | yes _ = refl , []
... | no ¬p = ⊥-elim-irr (¬p p)
⊩ᴱ-elim Unitᴰ  δ Unitₑ      = refl , []
⊩ᴱ-elim Boolᴰ  δ Boolₑ      = refl , []
⊩ᴱ-elim Natᴰ   δ Natₑ       = refl , []
⊩ᴱ-elim Emptyᴰ δ Emptyₑ     = refl , []
⊩ᴱ-elim |×|ᴰ   δ (p |×|ₑ q) = refl , p ∷ q ∷ []
⊩ᴱ-elim |+|ᴰ   δ (p |+|ₑ q) = refl , p ∷ q ∷ []
⊩ᴱ-elim |List|ᴰ δ (|List|ₑ p) = refl , p ∷ []

-- The value-type parts of a type are smaller than it

infix 4 _≺_

data _≺_ {Ψ : Scope} (X A : OVType Ψ) : Set where
  left  : ∀ {B ps v Y} → Decomp A B ps → ty v X Y ∈ ps → X ≺ A
  right : ∀ {B ps v Y} → Decomp B A ps → ty v Y X ∈ ps → X ≺ A

Accˡ Accʳ : ∀ {Ψ} → Part Ψ → Set
Accˡ (ty _ X _) = Acc _≺_ X
Accˡ (rg _ _ _) = ⊤
Accˡ (eg _ _ _) = ⊤
Accʳ (ty _ _ Y) = Acc _≺_ Y
Accʳ (rg _ _ _) = ⊤
Accʳ (eg _ _ _) = ⊤

≺-wf : ∀ {Ψ} → (A : OVType Ψ) → Acc _≺_ A

-- The accessibility of the parts of a type, on either side

accs : ∀ {Ψ} → (A : OVType Ψ)
     → (∀ {B ps} → Decomp A B ps → All Accˡ ps) × (∀ {B ps} → Decomp B A ps → All Accʳ ps)
accs (tvar α)      = (λ ()) , (λ ())
accs (Base b)      = (λ { Baseᴰ → [] }) , (λ { Baseᴰ → [] })
accs Unit          = (λ { Unitᴰ → [] }) , (λ { Unitᴰ → [] })
accs Bool          = (λ { Boolᴰ → [] }) , (λ { Boolᴰ → [] })
accs Nat           = (λ { Natᴰ → [] }) , (λ { Natᴰ → [] })
accs Empty         = (λ { Emptyᴰ → [] }) , (λ { Emptyᴰ → [] })
accs (A |×| B)     = (λ { |×|ᴰ → ≺-wf A ∷ ≺-wf B ∷ [] })
                   , (λ { |×|ᴰ → ≺-wf A ∷ ≺-wf B ∷ [] })
accs (A |+| B)     = (λ { |+|ᴰ → ≺-wf A ∷ ≺-wf B ∷ [] })
                   , (λ { |+|ᴰ → ≺-wf A ∷ ≺-wf B ∷ [] })
accs (|List| A)    = (λ { |List|ᴰ → ≺-wf A ∷ [] }) , (λ { |List|ᴰ → ≺-wf A ∷ [] })
accs (A ⇒ (B ‼ ε)) = (λ { ⇒ᴰ → ≺-wf A ∷ ≺-wf B ∷ tt ∷ [] })
                   , (λ { ⇒ᴰ → ≺-wf A ∷ ≺-wf B ∷ tt ∷ [] })
accs ([ ρ ] A)     = (λ { []ᴰ → tt ∷ ≺-wf A ∷ [] }) , (λ { []ᴰ → tt ∷ ≺-wf A ∷ [] })

≺-wf A = acc λ { (left g m)  → lookup (proj₁ (accs A) g) m
               ; (right g m) → lookup (proj₂ (accs A) g) m }
