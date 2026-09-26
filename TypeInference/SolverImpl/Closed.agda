------------------------------------------------------------------
-- Closed grade orderings                                       --
--                                                              --
-- A grade expression without unknowns has a value. An ordering --
-- between two such expressions is decided by the grade's own   --
-- `_≾?_`: `closedᴴ` drops each one that holds and fails on one --
-- that does not. The orderings decided are those of the set    --
-- and those it entails by transitivity, namely two closed      --
-- sides joined by a chain of orderings whose sides are         --
-- compared syntactically (`Transitive`, over `Reach`). A       --
-- var-rule disjunction whose grade has a value is decided      --
-- against the unit in the same way: it is dropped when the     --
-- ordering holds, and the check fails when the ordering does   --
-- not hold and the type is refuted eternal (`etDec`).          --
--                                                              --
-- Contract. The result entails the set (`closedᴴ-⊩`) and is    --
-- entailed wherever the set is (`closedᴴ-⊆`); a failure leaves --
-- the set unsatisfiable (`closedᴴ-fail`). Only closed atoms    --
-- are decided; the others are kept unchanged.                  --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁻; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using () renaming (ε to ◅-nil; _◅_ to _◅◅_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (does)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Closed (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S
  using (Satisfiable; VarOK-∅; closed-≾ᵣ; closed-≾ᵣ⁻; closed-≾ₑ; closed-≾ₑ⁻; inst-≡̂ᵣ)

open import TypeInference.SolverImpl.Resid S using (etDec; etDec-refute)
import TypeInference.SolverImpl.Reach as Reachability

------------------------------------------------------------------------
-- The value of an expression with no unknowns

valᵉ? : ∀ {Θ} → EExp Θ → Maybe E
valᵉ? (evar i)   = nothing
valᵉ? (econst c) = just c
valᵉ? (ε ·̂ₑ ε') with valᵉ? ε | valᵉ? ε'
... | just c | just c' = just (c ·ₑ c')
... | _      | _       = nothing
valᵉ? (ε ⊔̂ₑ ε') with valᵉ? ε | valᵉ? ε'
... | just c | just c' = just (c ⊔ₑ c')
... | _      | _       = nothing

valʳ? : ∀ {Θ} → RExp Θ → Maybe R
valʳ? (rvar i)   = nothing
valʳ? (rconst c) = just c
valʳ? (ρ ·̂ᵣ ρ') with valʳ? ρ | valʳ? ρ'
... | just c | just c' = just (c ·ᵣ c')
... | _      | _       = nothing
valʳ? (ρ ⊔̂ᵣ ρ') with valʳ? ρ | valʳ? ρ'
... | just c | just c' = just (c ⊔ᵣ c')
... | _      | _       = nothing
valʳ? ∣ ε ∣̂ᵉ with valᵉ? ε
... | just c  = just (mapᵉ c)
... | nothing = nothing

-- An expression with a value is convertible to it

convᵉ : ∀ {Θ} {c : E} → (ε : EExp Θ) → valᵉ? ε ≡ just c → ε ≡̂ₑ econst c
convᵉ (evar i) ()
convᵉ (econst c) refl = ≡̂ₑ-refl
convᵉ (ε ·̂ₑ ε') q with valᵉ? ε in e₁ | valᵉ? ε' in e₂
convᵉ (ε ·̂ₑ ε') refl | just c | just c' =
  ≡̂ₑ-trans (≡̂ₑ-cong (convᵉ ε e₁) (convᵉ ε' e₂)) ≡̂ₑ-const-·
convᵉ (ε ·̂ₑ ε') () | just _  | nothing
convᵉ (ε ·̂ₑ ε') () | nothing | _
convᵉ (ε ⊔̂ₑ ε') q with valᵉ? ε in e₁ | valᵉ? ε' in e₂
convᵉ (ε ⊔̂ₑ ε') refl | just c | just c' =
  ≡̂ₑ-trans (≡̂ₑ-cong-⊔ (convᵉ ε e₁) (convᵉ ε' e₂)) ≡̂ₑ-const-⊔
convᵉ (ε ⊔̂ₑ ε') () | just _  | nothing
convᵉ (ε ⊔̂ₑ ε') () | nothing | _

convʳ : ∀ {Θ} {c : R} → (ρ : RExp Θ) → valʳ? ρ ≡ just c → ρ ≡̂ᵣ rconst c
convʳ (rvar i) ()
convʳ (rconst c) refl = ≡̂ᵣ-refl
convʳ (ρ ·̂ᵣ ρ') q with valʳ? ρ in e₁ | valʳ? ρ' in e₂
convʳ (ρ ·̂ᵣ ρ') refl | just c | just c' =
  ≡̂ᵣ-trans (≡̂ᵣ-cong (convʳ ρ e₁) (convʳ ρ' e₂)) ≡̂ᵣ-const-·
convʳ (ρ ·̂ᵣ ρ') () | just _  | nothing
convʳ (ρ ·̂ᵣ ρ') () | nothing | _
convʳ (ρ ⊔̂ᵣ ρ') q with valʳ? ρ in e₁ | valʳ? ρ' in e₂
convʳ (ρ ⊔̂ᵣ ρ') refl | just c | just c' =
  ≡̂ᵣ-trans (≡̂ᵣ-cong-⊔ (convʳ ρ e₁) (convʳ ρ' e₂)) ≡̂ᵣ-const-⊔
convʳ (ρ ⊔̂ᵣ ρ') () | just _  | nothing
convʳ (ρ ⊔̂ᵣ ρ') () | nothing | _
convʳ ∣ ε ∣̂ᵉ q with valᵉ? ε in e
convʳ ∣ ε ∣̂ᵉ refl | just c = ≡̂ᵣ-trans (≡̂ᵣ-map-cong (convᵉ ε e)) ≡̂ᵣ-map-const
convʳ ∣ ε ∣̂ᵉ ()   | nothing

------------------------------------------------------------------------
-- Deciding the closed orderings of a list

-- A closed ordering that fails

Falseʳ : ∀ {Θ} → List (RExp Θ × RExp Θ) → Set
Falseʳ {Θ} l = Σ[ ρ ∈ RExp Θ ] Σ[ ρ' ∈ RExp Θ ] Σ[ c ∈ R ] Σ[ c' ∈ R ]
                 ((ρ , ρ') ∈ l × valʳ? ρ ≡ just c × valʳ? ρ' ≡ just c' × ¬ (c ≾ᵣ c'))

Falseᵉ : ∀ {Θ} → List (EExp Θ × EExp Θ) → Set
Falseᵉ {Θ} l = Σ[ ε ∈ EExp Θ ] Σ[ ε' ∈ EExp Θ ] Σ[ c ∈ E ] Σ[ c' ∈ E ]
                 ((ε , ε') ∈ l × valᵉ? ε ≡ just c × valᵉ? ε' ≡ just c' × ¬ (c ≾ₑ c'))

-- The orderings left once the closed ones that hold are dropped

record Keptʳ {Θ : Scope} (l : List (RExp Θ × RExp Θ)) : Set where
  constructor keptʳ
  field
    lʳ   : List (RExp Θ × RExp Θ)
    subʳ : ∀ {p} → p ∈ lʳ → p ∈ l
    entʳ : ∀ {Θ'} {Q : Hyps Θ'} → (δ : Subst Θ Θ')
         → (∀ {ρ ρ'} → (ρ , ρ') ∈ lʳ → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ)
         → ∀ {ρ ρ'} → (ρ , ρ') ∈ l → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ

record Keptᵉ {Θ : Scope} (l : List (EExp Θ × EExp Θ)) : Set where
  constructor keptᵉ
  field
    lᵉ   : List (EExp Θ × EExp Θ)
    subᵉ : ∀ {p} → p ∈ lᵉ → p ∈ l
    entᵉ : ∀ {Θ'} {Q : Hyps Θ'} → (δ : Subst Θ Θ')
         → (∀ {ε ε'} → (ε , ε') ∈ lᵉ → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ)
         → ∀ {ε ε'} → (ε , ε') ∈ l → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ

open Keptʳ
open Keptᵉ

consʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} {ρ ρ'} → Keptʳ l → Keptʳ ((ρ , ρ') ∷ l)
consʳ {ρ = ρ} {ρ'} k =
  keptʳ ((ρ , ρ') ∷ lʳ k)
        (λ { (here refl) → here refl ; (there m) → there (subʳ k m) })
        (λ δ f → λ { (here refl) → f (here refl)
                   ; (there m)   → entʳ k δ (λ m' → f (there m')) m })

consᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} {ε ε'} → Keptᵉ l → Keptᵉ ((ε , ε') ∷ l)
consᵉ {ε = ε} {ε'} k =
  keptᵉ ((ε , ε') ∷ lᵉ k)
        (λ { (here refl) → here refl ; (there m) → there (subᵉ k m) })
        (λ δ f → λ { (here refl) → f (here refl)
                   ; (there m)   → entᵉ k δ (λ m' → f (there m')) m })

dropʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} {ρ ρ' c c'}
      → valʳ? ρ ≡ just c → valʳ? ρ' ≡ just c' → c ≾ᵣ c'
      → Keptʳ l → Keptʳ ((ρ , ρ') ∷ l)
dropʳ {ρ = ρ} {ρ'} q q' p k =
  keptʳ (lʳ k) (λ m → there (subʳ k m))
        (λ δ f → λ { (here refl) → closed-≾ᵣ⁻ (convʳ ρ q) (convʳ ρ' q') δ p
                   ; (there m)   → entʳ k δ f m })

dropᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} {ε ε' c c'}
      → valᵉ? ε ≡ just c → valᵉ? ε' ≡ just c' → c ≾ₑ c'
      → Keptᵉ l → Keptᵉ ((ε , ε') ∷ l)
dropᵉ {ε = ε} {ε'} q q' p k =
  keptᵉ (lᵉ k) (λ m → there (subᵉ k m))
        (λ δ f → λ { (here refl) → closed-≾ₑ⁻ (convᵉ ε q) (convᵉ ε' q') δ p
                   ; (there m)   → entᵉ k δ f m })

thereʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} {p} → Falseʳ l → Falseʳ (p ∷ l)
thereʳ (ρ , ρ' , c , c' , m , q , q' , n) = ρ , ρ' , c , c' , there m , q , q' , n

thereᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} {p} → Falseᵉ l → Falseᵉ (p ∷ l)
thereᵉ (ε , ε' , c , c' , m , q , q' , n) = ε , ε' , c , c' , there m , q , q' , n

closedʳ : ∀ {Θ} → (l : List (RExp Θ × RExp Θ)) → Falseʳ l ⊎ Keptʳ l
closedʳ [] = inj₂ (keptʳ [] (λ ()) (λ δ k → λ ()))
closedʳ ((ρ , ρ') ∷ l) with closedʳ l
... | inj₁ f = inj₁ (thereʳ f)
... | inj₂ k with valʳ? ρ in q | valʳ? ρ' in q'
...   | just c  | just c' with c ≾ᵣ? c'
...     | yes p = inj₂ (dropʳ q q' p k)
...     | no n  = inj₁ (ρ , ρ' , c , c' , here refl , q , q' , n)
closedʳ ((ρ , ρ') ∷ l) | inj₂ k | just _  | nothing = inj₂ (consʳ k)
closedʳ ((ρ , ρ') ∷ l) | inj₂ k | nothing | _       = inj₂ (consʳ k)

closedᵉ : ∀ {Θ} → (l : List (EExp Θ × EExp Θ)) → Falseᵉ l ⊎ Keptᵉ l
closedᵉ [] = inj₂ (keptᵉ [] (λ ()) (λ δ k → λ ()))
closedᵉ ((ε , ε') ∷ l) with closedᵉ l
... | inj₁ f = inj₁ (thereᵉ f)
... | inj₂ k with valᵉ? ε in q | valᵉ? ε' in q'
...   | just c  | just c' with c ≾ₑ? c'
...     | yes p = inj₂ (dropᵉ q q' p k)
...     | no n  = inj₁ (ε , ε' , c , c' , here refl , q , q' , n)
closedᵉ ((ε , ε') ∷ l) | inj₂ k | just _  | nothing = inj₂ (consᵉ k)
closedᵉ ((ε , ε') ∷ l) | inj₂ k | nothing | _       = inj₂ (consᵉ k)

------------------------------------------------------------------------
-- Var-rule disjunctions

-- A disjunction whose grade has a value above the unit, at a type
-- refuted eternal

Falseᵈ : ∀ {Θ} → List (OVType Θ × RExp Θ) → Set
Falseᵈ {Θ} l = Σ[ A ∈ OVType Θ ] Σ[ ρ ∈ RExp Θ ] Σ[ c ∈ R ]
                 ((A , ρ) ∈ l × etDec A ≡ nothing × valʳ? ρ ≡ just c × ¬ (c ≾ᵣ uᵣ))

record Keptᵈ {Θ : Scope} (l : List (OVType Θ × RExp Θ)) : Set where
  constructor keptᵈ
  field
    lᵈ   : List (OVType Θ × RExp Θ)
    subᵈ : ∀ {p} → p ∈ lᵈ → p ∈ l
    entᵈ : ∀ {Θ'} {Q : Hyps Θ'} → (δ : Subst Θ Θ')
         → (∀ {A ρ} → (A , ρ) ∈ lᵈ → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ))
         → ∀ {A ρ} → (A , ρ) ∈ l → VarOK Q (A [ δ ]ᵛ) (ρ [ δ ]ʳ)

open Keptᵈ

consᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} {A ρ} → Keptᵈ l → Keptᵈ ((A , ρ) ∷ l)
consᵈ {A = A} {ρ} k =
  keptᵈ ((A , ρ) ∷ lᵈ k)
        (λ { (here refl) → here refl ; (there m) → there (subᵈ k m) })
        (λ δ f → λ { (here refl) → f (here refl)
                   ; (there m)   → entᵈ k δ (λ m' → f (there m')) m })

dropᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} {A ρ c}
      → valʳ? ρ ≡ just c → c ≾ᵣ uᵣ → Keptᵈ l → Keptᵈ ((A , ρ) ∷ l)
dropᵈ {ρ = ρ} q p k =
  keptᵈ (lᵈ k) (λ m → there (subᵈ k m))
        (λ δ f → λ { (here refl) → ≾ᵘ-ok (transᵣ (eqᵣ (≡̂ᵣ-subst δ (convʳ ρ q))) (atomᵣ p))
                   ; (there m)   → entᵈ k δ f m })

thereᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} {p} → Falseᵈ l → Falseᵈ (p ∷ l)
thereᵈ (A , ρ , c , m , e , q , n) = A , ρ , c , there m , e , q , n

closedᵈ : ∀ {Θ} → (l : List (OVType Θ × RExp Θ)) → Falseᵈ l ⊎ Keptᵈ l
closedᵈ [] = inj₂ (keptᵈ [] (λ ()) (λ δ k → λ ()))
closedᵈ ((A , ρ) ∷ l) with closedᵈ l
... | inj₁ f = inj₁ (thereᵈ f)
... | inj₂ k with valʳ? ρ in q
...   | nothing = inj₂ (consᵈ k)
...   | just c with c ≾ᵣ? uᵣ
...     | yes p = inj₂ (dropᵈ q p k)
...     | no n with etDec A in e
...       | nothing = inj₁ (A , ρ , c , here refl , e , q , n)
...       | just _  = inj₂ (consᵈ k)

falseᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} → Falseᵈ l → (δ : Subst Θ ∅ˢ)
       → (∀ {A ρ} → (A , ρ) ∈ l → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ)) → ⊥
falseᵈ (A , ρ , c , m , e , q , n) δ k with VarOK-∅ (k m)
... | inj₁ et = etDec-refute A e δ et
... | inj₂ le = n (subst (_≾ᵣ uᵣ) (inst-≡̂ᵣ δ (convʳ ρ q)) le)

------------------------------------------------------------------------
-- A failing closed ordering holds at no closed instance

falseʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} → Falseʳ l → (δ : Subst Θ ∅ˢ)
       → (∀ {ρ ρ'} → (ρ , ρ') ∈ l → ∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ) → ⊥
falseʳ (ρ , ρ' , c , c' , m , q , q' , n) δ k =
  n (closed-≾ᵣ (convʳ ρ q) (convʳ ρ' q') δ (k m))

falseᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} → Falseᵉ l → (δ : Subst Θ ∅ˢ)
       → (∀ {ε ε'} → (ε , ε') ∈ l → ∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ) → ⊥
falseᵉ (ε , ε' , c , c' , m , q , q' , n) δ k =
  n (closed-≾ₑ (convᵉ ε q) (convᵉ ε' q') δ (k m))

------------------------------------------------------------------------
-- The orderings a list entails by transitivity
--
-- The sides of the orderings are the vertices of a graph and each
-- ordering an edge, closed by `Reach`. A pair of closed sides joined
-- by a chain of two or more edges is entailed; a shorter chain is an
-- ordering of the list or reflexive.

module Transitive {X : Set} (_≟_ : DecidableEquality X) (closed? : X → 𝔹)
                  (l : List (X × X)) where

  Edge : X → X → Set
  Edge a b = (a , b) ∈ l

  private

    edgesOf : (k : List (X × X)) → (∀ {p} → p ∈ k → p ∈ l)
            → List (Σ[ a ∈ X ] Σ[ b ∈ X ] Edge a b)
    edgesOf []            f = []
    edgesOf ((a , b) ∷ k) f = (a , b , f (here refl)) ∷ edgesOf k (λ m → f (there m))

    insert : X → List X → List X
    insert x xs with any (λ y → does (x ≟ y)) xs
    ... | true  = xs
    ... | false = x ∷ xs

    sides : List (X × X) → List X
    sides []            = []
    sides ((a , b) ∷ k) = insert a (insert b (sides k))

  vs : List X
  vs = sides l

  open Reachability _≟_ Edge (edgesOf l (λ m → m)) vs using (Chain; Closure; closure; reach)

  private

    closedOf : (k : List X) → (∀ {x} → x ∈ k → x ∈ vs) → List (Σ[ a ∈ X ] a ∈ vs)
    closedOf []      f = []
    closedOf (a ∷ k) f with closed? a
    ... | true  = (a , f (here refl)) ∷ closedOf k (λ m → f (there m))
    ... | false = closedOf k (λ m → f (there m))

    long : ∀ {a b} → Chain a b → 𝔹
    long (_ ◅◅ _ ◅◅ _) = true
    long _             = false

    from : Closure → List (Σ[ b ∈ X ] b ∈ vs) → Σ[ a ∈ X ] a ∈ vs
         → List (Σ[ a ∈ X ] Σ[ b ∈ X ] Chain a b)
    from C []              _        = []
    from C ((b , mb) ∷ bs) (a , ma) with reach C ma mb
    ... | nothing = from C bs (a , ma)
    ... | just p with long p
    ...   | true  = (a , b , p) ∷ from C bs (a , ma)
    ...   | false = from C bs (a , ma)

    among : Closure → List (Σ[ a ∈ X ] a ∈ vs) → List (Σ[ a ∈ X ] Σ[ b ∈ X ] Chain a b)
    among C cs = concatMap (from C cs) cs

    ends : (Σ[ a ∈ X ] Σ[ b ∈ X ] Chain a b) → X × X
    ends (a , b , _) = a , b

  -- The pairs of closed sides joined by a chain of two or more edges

  chains : List (X × X)
  chains = map ends (among closure (closedOf vs (λ m → m)))

  -- Each holds wherever the orderings do, in a preorder

  chains-⊩ : {Le : X → X → Set} → (∀ {a} → Le a a) → (∀ {a b c} → Le a b → Le b c → Le a c)
           → (∀ {a b} → (a , b) ∈ l → Le a b) → ∀ {a b} → (a , b) ∈ chains → Le a b
  chains-⊩ {Le} r t e m with ∈-map⁻ ends m
  ... | (a , b , p) , _ , refl = along p
    where
      along : ∀ {a b} → Chain a b → Le a b
      along ◅-nil     = r
      along (x ◅◅ xs) = t (e x) (along xs)

-- The resource and effect orderings, with those they entail by
-- transitivity between closed sides

withChainsʳ : ∀ {Θ} → List (RExp Θ × RExp Θ) → List (RExp Θ × RExp Θ)
withChainsʳ l = l ++ Transitive.chains _≟ʳ_ (λ ρ → is-just (valʳ? ρ)) l

withChainsᵉ : ∀ {Θ} → List (EExp Θ × EExp Θ) → List (EExp Θ × EExp Θ)
withChainsᵉ l = l ++ Transitive.chains _≟ᵉ_ (λ ε → is-just (valᵉ? ε)) l

withChainsʳ-⊩ : ∀ {Θ Θ'} {Q : Hyps Θ'} {δ : Subst Θ Θ'} → (l : List (RExp Θ × RExp Θ))
              → (∀ {ρ ρ'} → (ρ , ρ') ∈ l → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ)
              → ∀ {ρ ρ'} → (ρ , ρ') ∈ withChainsʳ l → Q ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ
withChainsʳ-⊩ l h m with ∈-++⁻ l m
... | inj₁ m' = h m'
... | inj₂ m' =
  Transitive.chains-⊩ _≟ʳ_ (λ ρ → is-just (valʳ? ρ)) l ⊩≾̂ᵣ-refl transᵣ h m'

withChainsᵉ-⊩ : ∀ {Θ Θ'} {Q : Hyps Θ'} {δ : Subst Θ Θ'} → (l : List (EExp Θ × EExp Θ))
              → (∀ {ε ε'} → (ε , ε') ∈ l → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ)
              → ∀ {ε ε'} → (ε , ε') ∈ withChainsᵉ l → Q ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ
withChainsᵉ-⊩ l h m with ∈-++⁻ l m
... | inj₁ m' = h m'
... | inj₂ m' =
  Transitive.chains-⊩ _≟ᵉ_ (λ ε → is-just (valᵉ? ε)) l ⊩≾̂ₑ-refl transₑ h m'

------------------------------------------------------------------------
-- The closed orderings of a hypothesis set decided

closedᴴ : ∀ {Θ} → Hyps Θ → Maybe (Hyps Θ)
closedᴴ Q with closedʳ (withChainsʳ (ordᵣ Q)) | closedᵉ (withChainsᵉ (ordₑ Q)) | closedᵈ (disj Q)
... | inj₂ kʳ | inj₂ kᵉ | inj₂ kᵈ =
      just (hyps (ets Q) (subᵥ Q) (lʳ kʳ) (lᵉ kᵉ) (lᵈ kᵈ))
... | _       | _       | _       = nothing

-- What is left entails the set

closedᴴ-⊩ : ∀ {Θ} → (Q : Hyps Θ) → {Q₁ : Hyps Θ} → closedᴴ Q ≡ just Q₁ → Q₁ ⊩ᴴ Q [ idˢ ]
closedᴴ-⊩ Q eq with closedʳ (withChainsʳ (ordᵣ Q)) | closedᵉ (withChainsᵉ (ordₑ Q)) | closedᵈ (disj Q)
closedᴴ-⊩ Q refl | inj₂ kʳ | inj₂ kᵉ | inj₂ kᵈ =
  mk⊩ᴴ (⊩ets r) (⊩subᵥ r) (λ m → entʳ kʳ idˢ (⊩ordᵣ r) (∈-++⁺ˡ m))
       (λ m → entᵉ kᵉ idˢ (⊩ordₑ r) (∈-++⁺ˡ m)) (entᵈ kᵈ idˢ (⊩disj r))
  where r = ⊩ᴴ-refl {Q = hyps (ets Q) (subᵥ Q) (lʳ kʳ) (lᵉ kᵉ) (lᵈ kᵈ)}
closedᴴ-⊩ Q () | inj₁ _ | _      | _
closedᴴ-⊩ Q () | inj₂ _ | inj₁ _ | _
closedᴴ-⊩ Q () | inj₂ _ | inj₂ _ | inj₁ _

-- and is entailed wherever the set is

closedᴴ-⊆ : ∀ {Θ Θ'} → (Q : Hyps Θ) → {Q₁ : Hyps Θ} → closedᴴ Q ≡ just Q₁
          → {Q' : Hyps Θ'} {δ : Subst Θ Θ'} → Q' ⊩ᴴ Q [ δ ] → Q' ⊩ᴴ Q₁ [ δ ]
closedᴴ-⊆ Q eq h with closedʳ (withChainsʳ (ordᵣ Q)) | closedᵉ (withChainsᵉ (ordₑ Q)) | closedᵈ (disj Q)
closedᴴ-⊆ Q refl h | inj₂ kʳ | inj₂ kᵉ | inj₂ kᵈ =
  mk⊩ᴴ (⊩ets h) (⊩subᵥ h) (λ m → withChainsʳ-⊩ (ordᵣ Q) (⊩ordᵣ h) (subʳ kʳ m))
       (λ m → withChainsᵉ-⊩ (ordₑ Q) (⊩ordₑ h) (subᵉ kᵉ m))
       (λ m → ⊩disj h (subᵈ kᵈ m))
closedᴴ-⊆ Q () h | inj₁ _ | _      | _
closedᴴ-⊆ Q () h | inj₂ _ | inj₁ _ | _
closedᴴ-⊆ Q () h | inj₂ _ | inj₂ _ | inj₁ _

-- A failure leaves the set unsatisfiable

closedᴴ-fail : ∀ {Θ} → (Q : Hyps Θ) → closedᴴ Q ≡ nothing → ¬ Satisfiable Q []
closedᴴ-fail Q eq (δ , h ∷ []) with closedʳ (withChainsʳ (ordᵣ Q)) | closedᵉ (withChainsᵉ (ordₑ Q)) | closedᵈ (disj Q)
... | inj₁ f | _      | _      = falseʳ f δ (withChainsʳ-⊩ (ordᵣ Q) (⊩ordᵣ h))
... | inj₂ _ | inj₁ f | _      = falseᵉ f δ (withChainsᵉ-⊩ (ordₑ Q) (⊩ordₑ h))
... | inj₂ _ | inj₂ _ | inj₁ f = falseᵈ f δ (⊩disj h)
closedᴴ-fail Q () (δ , h ∷ []) | inj₂ _ | inj₂ _ | inj₂ _
