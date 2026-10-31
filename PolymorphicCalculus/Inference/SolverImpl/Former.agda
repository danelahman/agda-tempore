------------------------------------------------------------------
-- Type formers and the variance of their parts                 --
--                                                              --
-- An open type other than a type variable is a former applied  --
-- to its parts: value types, box grades and effects. The       --
-- variance table `Decomp A B ps` says `A` and `B` have one     --
-- former and pairs their parts with variance (`co`, `contra`,  --
-- `inv`) and sort (`ty`, `rg`, `eg`); `decompose` decides it,  --
-- `self` reads it off one type, and `eternal` is the           --
-- eternality column.                                           --
--                                                              --
-- The table is exact at every pair of instances: subtyping     --
-- holds exactly when every pair of parts holds at its variance --
-- (`<:-intro`, `<:-elim`), eternality exactly when the column  --
-- admits the former and every value-type part is eternal       --
-- (`⊩ᴱ-intro`, `⊩ᴱ-elim`). Recursion along the table is well   --
-- founded (`_≺_`, `≺-wf`).                                     --
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

open import Grades.Base
open import Language.BaseTypes using (module BaseTypes)
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.SolverImpl.Former (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open BaseTypes BTs using (_≡ᵇ?_; eternalBaseType?)

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses               S

-- How the parts at one position of two types of one former are related by a
-- subtyping demand between them

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

data Part (Ω : Scope) : Set where
  ty : Variance → OVType Ω → OVType Ω → Part Ω    -- value types
  rg : Variance → RExp Ω → RExp Ω → Part Ω        -- resource grades
  eg : Variance → EExp Ω → EExp Ω → Part Ω        -- effect grades

infixl 50 _[_∣_]ᴾ

_[_∣_]ᴾ : ∀ {Ω Ω'} → Part Ω → Subst Ω Ω' → Subst Ω Ω' → Part Ω'
ty v A B [ σ ∣ τ ]ᴾ = ty v (A [ σ ]ᵛ) (B [ τ ]ᵛ)
rg v ρ ρ' [ σ ∣ τ ]ᴾ = rg v (ρ [ σ ]ʳ) (ρ' [ τ ]ʳ)
eg v ε ε' [ σ ∣ τ ]ᴾ = eg v (ε [ σ ]ᵉ) (ε' [ τ ]ᵉ)

-- The demand a pair of parts makes, at its variance

Holdsᴾ : ∀ {Ω} → Hyps Ω → Part Ω → Set
Holdsᴾ Q (ty v A B)  = At v (Q ∣_<:̂ᵛ_) A B
Holdsᴾ Q (rg v ρ ρ') = At v (Q ⊩_≾̂ᵣ_) ρ ρ'
Holdsᴾ Q (eg v ε ε') = At v (Q ⊩_≾̂ₑ_) ε ε'

-- The variance table

data Decomp {Ω : Scope} : OVType Ω → OVType Ω → List (Part Ω) → Set where
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
  ⇛ᴰ     : ∀ {A A' B B' ε η ε' η'}
         → Decomp (A ‼ ε ⇛ B ‼ ε') (A' ‼ η ⇛ B' ‼ η')
                  (ty contra A A' ∷ eg contra ε η ∷ ty co B B' ∷ eg co ε' η' ∷ [])

-- Two types: a pair of type variables, one former, or a clash

data Shape {Ω : Scope} : OVType Ω → OVType Ω → Set where
  vars  : (α β : TyVar Ω) → Shape (tvar α) (tvar β)
  parts : ∀ {A B} → (ps : List (Part Ω)) → Decomp A B ps → Shape A B
  clash : ∀ {A B} → Shape A B

decompose : ∀ {Ω} → (A B : OVType Ω) → Shape A B
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
decompose (A ‼ ε ⇛ B ‼ ε') (A' ‼ η ⇛ B' ‼ η') = parts _ ⇛ᴰ
decompose _              _                 = clash

-- One type: a type variable, or its former against itself, its pairs diagonal

Diag : ∀ {Ω} → Part Ω → Set
Diag (ty _ A B)  = A ≡ B
Diag (rg _ ρ ρ') = ρ ≡ ρ'
Diag (eg _ ε ε') = ε ≡ ε'

data Self {Ω : Scope} : OVType Ω → Set where
  var  : (α : TyVar Ω) → Self (tvar α)
  form : ∀ {A} → (ps : List (Part Ω)) → Decomp A A ps → All Diag ps → Self A

self : ∀ {Ω} → (A : OVType Ω) → Self A
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
self (A ‼ ε ⇛ B ‼ ε') = form _ ⇛ᴰ (refl ∷ refl ∷ refl ∷ refl ∷ [])

-- The eternality column

eternal : ∀ {Ω} {A B : OVType Ω} {ps} → Decomp A B ps → 𝔹
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
eternal ⇛ᴰ          = false

-- The table is exact for subtyping, at every pair of instances

<:-intro : ∀ {Ω Ω'} {Q : Hyps Ω'} {A B : OVType Ω} {ps} → Decomp A B ps
         → (σ τ : Subst Ω Ω') → All (λ p → Holdsᴾ Q (p [ σ ∣ τ ]ᴾ)) ps
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
<:-intro ⇛ᴰ     σ τ (p ∷ e ∷ q ∷ e' ∷ []) = (p ‼ₛ e) ⇛ₛ (q ‼ₛ e')

<:-elim : ∀ {Ω Ω'} {Q : Hyps Ω'} {A B : OVType Ω} {ps} → Decomp A B ps
        → (σ τ : Subst Ω Ω') → Q ∣ A [ σ ]ᵛ <:̂ᵛ B [ τ ]ᵛ
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
<:-elim ⇛ᴰ     σ τ ((p ‼ₛ e) ⇛ₛ (q ‼ₛ e')) = p ∷ e ∷ q ∷ e' ∷ []

-- The table is exact for eternality, at every instance; a grade part demands nothing

Etᴾ : ∀ {Ω} → Hyps Ω → Part Ω → Set
Etᴾ Q (ty _ A _) = Q ⊩ᴱ A
Etᴾ Q (rg _ _ _) = ⊤
Etᴾ Q (eg _ _ _) = ⊤

⊩ᴱ-intro : ∀ {Ω Ω'} {Q : Hyps Ω'} {A B : OVType Ω} {ps} → (g : Decomp A B ps)
         → eternal g ≡ true → (δ : Subst Ω Ω')
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

⊩ᴱ-elim : ∀ {Ω Ω'} {Q : Hyps Ω'} {A B : OVType Ω} {ps} → (g : Decomp A B ps)
        → (δ : Subst Ω Ω') → Q ⊩ᴱ A [ δ ]ᵛ
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

data _≺_ {Ω : Scope} (X A : OVType Ω) : Set where
  left  : ∀ {B ps v Y} → Decomp A B ps → ty v X Y ∈ ps → X ≺ A
  right : ∀ {B ps v Y} → Decomp B A ps → ty v Y X ∈ ps → X ≺ A

Accˡ Accʳ : ∀ {Ω} → Part Ω → Set
Accˡ (ty _ X _) = Acc _≺_ X
Accˡ (rg _ _ _) = ⊤
Accˡ (eg _ _ _) = ⊤
Accʳ (ty _ _ Y) = Acc _≺_ Y
Accʳ (rg _ _ _) = ⊤
Accʳ (eg _ _ _) = ⊤

≺-wf : ∀ {Ω} → (A : OVType Ω) → Acc _≺_ A

-- The accessibility of the parts of a type, on either side

accs : ∀ {Ω} → (A : OVType Ω)
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
accs (A ‼ ε ⇛ B ‼ ε') = (λ { ⇛ᴰ → ≺-wf A ∷ tt ∷ ≺-wf B ∷ tt ∷ [] })
                     , (λ { ⇛ᴰ → ≺-wf A ∷ tt ∷ ≺-wf B ∷ tt ∷ [] })

≺-wf A = acc λ { (left g m)  → lookup (proj₁ (accs A) g) m
               ; (right g m) → lookup (proj₂ (accs A) g) m }
