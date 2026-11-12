--------------------------------------------------------------------
-- The search for a closed instance of a solution                 --
--                                                                --
-- `search` reads a solution as a residual (`asResid`) under one  --
-- fresh rigid, so that every unknown is local, localises it      --
-- (`localiseAll`), retries the deferred conditions, reads the    --
-- atoms back and runs the closed check and the failing chains.   --
-- Each step can refute; otherwise the residual left is open.     --
--                                                                --
-- `establish` searches an open residual one class of shared      --
-- unknowns at a time (`components`), over the candidates of each --
-- unknown (`candsₑ`, `candsᵣ`: the unit, the top, the class's    --
-- constants, the hints' witnesses), type unknowns at the unit    --
-- type, and verifies the instance found (`verify`).              --
--                                                                --
-- Contract. A refutation leaves the solution unsatisfiable       --
-- (`refutedˢ`); a closed instance of an open residual is one of  --
-- the solution (`openˢ`); an instance found is one of the        --
-- solution (`foundᵉ`). An undecided or exhausted search claims   --
-- nothing.                                                       --
--                                                                --
-- Exhaustive search over a finite domain per unknown, class by   --
-- class.                                                         --
--------------------------------------------------------------------

open import Data.Bool.Base using (true; false; _∨_; _∧_; not; if_then_else_) renaming (Bool to 𝔹)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; foldr; allFin; filterᵇ;
                                  deduplicate)
open import Data.Bool.ListAction using (any)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _+_; _⊔_) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (does; ⌊_⌋)

open import Grades.Base
open import Grades.Hints using (SystemHints; module SystemHintsInterface)
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Inference.SolverImpl.Search
  (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S))
  (opEnum : OpEnum S)
  where

open LanguageSpec S
open GradeSystemInterface Grades
open SystemHintsInterface hints

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses               S
open import PolymorphicCalculus.Hypotheses.Instances     S
  using (Satisfiable; _≾̂ᵣ?_; _≾̂ₑ?_; ⊩Et?; _<:̂ᵛ?_; Et∨≾ᵘ?; ⊨++ᵠ⇒; ⊨++ᵠ⇐; ⊩ᴴ⇒⊨)

open import PolymorphicCalculus.Inference.SolverImpl.Deferred  S hints
  using (⊩ᴰ→⊩ᴼˢ; ⊩ᴼˢ→⊩ᴰ; κ⟨_⟩; allOf; constsₑ; constsᵣ; _++²_)
open import PolymorphicCalculus.Inference.SolverImpl.Resid    S
open import PolymorphicCalculus.Inference.SolverImpl.Entail   S hints using (checkClosed; checkClosed-fail; failingChain)
open import PolymorphicCalculus.Inference.SolverImpl.Localise S hints using (Localised; localise; lσ; lR; lsnd; lcpl; latom;
                                                         Entry; anyᶠ)
open import PolymorphicCalculus.Inference.SolverImpl.Solve     S hints opEnum
  using (ordsOf; ordsOf-⊩; withDfs; retryᴰ; retryᵈ; retriedL; keptᵈ)
open import PolymorphicCalculus.Inference.SolverImpl.Vars      S using (Vars; vʳ; vᵉ; _∪ᵛ_; fvʳ; fvᵉ)
open import PolymorphicCalculus.Inference.SolverImpl.Strengthen S hints using (fvᵈ)

------------------------------------------------------------------------
-- A hypothesis set and deferred conditions as a residual

asResid : ∀ {Ω} → Hyps Ω → List (QOrd Ω) → Resid Ω
asResid Q D = resid (ordᵣ Q) (ordₑ Q) (map tvar (ets Q)) (map (mapᵖ tvar) (subᵥ Q)) (disj Q)
                    (qhyps Q ++ D)

asResid-⊩ : ∀ {Ω Ω'} {Q' : Hyps Ω'} {Q : Hyps Ω} {D : List (QOrd Ω)} {δ : Subst Ω Ω'}
          → Q' ⊩ᴴ Q [ δ ] → (∀ {E} → E ∈ D → Q' ⊩ᴼ E [ δ ]) → Q' ⊩ᴿ asResid Q D [ δ ]
asResid-⊩ {Q' = Q'} {Q} {δ = δ} h g =
  mk⊩ᴿ (⊩ordᵣ h) (⊩ordₑ h) ts' ss' (⊩disj h) (λ m → [ ⊩qhyps h , g ]′ (∈-++⁻ (qhyps Q) m))
  where
    ts' : ∀ {A} → A ∈ map tvar (ets Q) → Q' ⊩Et A [ δ ]ᵛ
    ts' m with ∈-map⁻ tvar m
    ... | α , m₀ , refl = ⊩ets h m₀

    ss' : ∀ {A B} → (A , B) ∈ map (mapᵖ tvar) (subᵥ Q) → Q' ⊩ A [ δ ]ᵛ <:̂ᵛ B [ δ ]ᵛ
    ss' m with ∈-map⁻ (mapᵖ tvar) m
    ... | (α , β) , m₀ , refl = ⊩subᵥ h m₀

⊩-asResid : ∀ {Ω Ω'} {Q : Hyps Ω} {D : List (QOrd Ω)} {δ : Subst Ω Ω'}
          → ∅ᴴ ⊩ᴿ asResid Q D [ δ ] → ∅ᴴ ⊩ᴴ Q [ δ ] × (∀ {E} → E ∈ D → ∅ᴴ ⊩ᴼ E [ δ ])
⊩-asResid {Q = Q} h =
  mk⊩ᴴ (λ m → ⊩ts h (∈-map⁺ tvar m)) (λ m → ⊩ss h (∈-map⁺ (mapᵖ tvar) m))
       (⊩rs h) (⊩es h) (⊩ds h) (λ m → ⊩dfs h (∈-++⁺ˡ m)) ,
  (λ m → ⊩dfs h (∈-++⁺ʳ (qhyps Q) m))

asResid-atomic : ∀ {Ω} {Q : Hyps Ω} {D : List (QOrd Ω)} → Atomicˢ (ss (asResid Q D))
asResid-atomic m with ∈-map⁻ (mapᵖ tvar) m
... | (α , β) , m₀ , refl = α , β , refl , refl

-- Weakening past an effect variable keeps subtyping demands atomic

atomic-wkᵉ : ∀ {Ω} {l : List (OVType Ω × OVType Ω)} → Atomicˢ l
           → Atomicˢ (map (mapᵖ (_[ wkˢᵉ ]ᵛ)) l)
atomic-wkᵉ at m with ∈-map⁻ (mapᵖ (_[ wkˢᵉ ]ᵛ)) m
... | (A , B) , m₀ , refl with at m₀
...   | α , β , refl , refl = α , β , refl , refl

------------------------------------------------------------------------
-- Every unknown local
--
-- The scope extended by one rigid, the only image of its entry; the weakened
-- residual does not mention it

rigid : ∀ {Ω} → Subst (∅ˢ +e) (Ω +e)
rigid = sub (λ ()) (λ ()) (λ { zero → evar zero })

localiseAll : ∀ {Ω} → (R : Resid Ω) → Localised (rigid {Ω}) (R [ wkˢᵉ ]ᴿ)
localiseAll R = localise rigid (R [ wkˢᵉ ]ᴿ)

-- A closed instance, lifted past the rigid, enters the scope

entry : ∀ {Ω} → (δ : Subst Ω ∅ˢ) → Entry (rigid {Ω}) (δ ↑ᵉ)
entry δ = idˢ , mk≐ˢ (λ ()) (λ ()) (λ { zero → refl })

-- and is a closed instance of the localised residual, the rigid at the unit

closedᴸ : ∀ {Ω} {R : Resid Ω} → (L : Localised (rigid {Ω}) (R [ wkˢᵉ ]ᴿ)) → (δ : Subst Ω ∅ˢ)
        → ∅ᴴ ⊩ᴿ R [ δ ] → ∅ᴴ ⊩ᴿ lR L [ δ ↑ᵉ ⨟ˢ κ⟨ 𝟏̂ₑ ⟩ ]
closedᴸ L δ h =
  ⊩ᴿ-⨟ ⊩ᴴ-∅
    (lcpl L (δ ↑ᵉ) (entry δ)
      (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wkˢᵉ-↑ᵉ δ)) (⊩ᴿ-⨟ ⊩ᴴ-∅ h))))

-- A closed instance of the localised residual is one of the residual

openᴸ : ∀ {Ω} {R : Resid Ω} → (L : Localised (rigid {Ω}) (R [ wkˢᵉ ]ᴿ))
      → (τ : Subst (Ω +e) ∅ˢ) → ∅ᴴ ⊩ᴿ lR L [ τ ] → ∅ᴴ ⊩ᴿ R [ wkˢᵉ ⨟ˢ (lσ L ⨟ˢ τ) ]
openᴸ L τ h = ⊩ᴿ-subst (lsnd L τ ∅ᴴ h)

------------------------------------------------------------------------
-- The search

data Search {Ω} (Q : Hyps Ω) (D : List (QOrd Ω)) : Set where
  refutedˢ : ¬ Satisfiable (Q ++ᵠ D) → Search Q D
  openˢ    : (R : Resid (Ω +e))
           → ((τ : Subst (Ω +e) ∅ˢ) → ∅ᴴ ⊩ᴿ R [ τ ] → Satisfiable (Q ++ᵠ D))
           → Search Q D

-- A subtyping demand between type variables always reads back

subDec-vars : ∀ {Ω} → (α β : TyVar Ω) → subDec {Ω} (tvar α) (tvar β) ≡ nothing → ⊥
subDec-vars α β ()

-- The search from a localisation of the solution's residual

searchᴸ : ∀ {Ω} → (Q : Hyps Ω) → (D : List (QOrd Ω))
        → Localised (rigid {Ω}) (asResid Q D [ wkˢᵉ ]ᴿ) → Search Q D
searchᴸ {Ω} Q D L = retried (retryᴰ (ordsOf (lR L)) (dfs (lR L)))
  where
    -- a closed instance of the solution, of the localised residual

    inst : Satisfiable (Q ++ᵠ D) → Σ[ τ ∈ Subst (Ω +e) ∅ˢ ] (∅ᴴ ⊩ᴿ lR L [ τ ])
    inst (δ , h) with ⊨++ᵠ⇒ {R = D} h
    ... | hQ , hD = δ ↑ᵉ ⨟ˢ κ⟨ 𝟏̂ₑ ⟩ , closedᴸ L δ (asResid-⊩ hQ (⊩ᴼˢ→⊩ᴰ {Q = ∅ᴴ} {δ = δ} D hD))

    -- and back

    sat : (τ : Subst (Ω +e) ∅ˢ) → ∅ᴴ ⊩ᴿ lR L [ τ ] → Satisfiable (Q ++ᵠ D)
    sat τ h = wkˢᵉ ⨟ˢ (lσ L ⨟ˢ τ) ,
              ⊨++ᵠ⇐ (proj₁ hs , ⊩ᴰ→⊩ᴼˢ {Q = ∅ᴴ} {δ = wkˢᵉ ⨟ˢ (lσ L ⨟ˢ τ)} D (proj₂ hs))
      where
        hs = ⊩-asResid {Q = Q} {D = D} (openᴸ L τ h)

    atomicᴸ : Atomicˢ (ss (lR L))
    atomicᴸ = latom L (atomic-wkᵉ (asResid-atomic {Q = Q} {D = D}))

    retried : _ → Search Q D
    retried (inj₁ (E , m , r)) =
      refutedˢ (λ s → r (proj₁ (inst s)) (⊩dfs (proj₂ (inst s)) m))
    retried (inj₂ (retriedL D' b f)) = readBack (toHyps R') refl
      where
        R' = withDfs (lR L) D'

        fwd : ∀ {τ} → ∅ᴴ ⊩ᴿ lR L [ τ ] → ∅ᴴ ⊩ᴿ R' [ τ ]
        fwd {τ} h = mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (⊩ss h) (⊩ds h) (f τ (⊩dfs h))

        bwd : ∀ {τ} → ∅ᴴ ⊩ᴿ R' [ τ ] → ∅ᴴ ⊩ᴿ lR L [ τ ]
        bwd {τ} h = mk⊩ᴿ (⊩rs h) (⊩es h) (⊩ts h) (⊩ss h) (⊩ds h)
                         (b τ (ordsOf-⊩ h) (⊩dfs h))

        inst' : Satisfiable (Q ++ᵠ D) → Σ[ τ ∈ Subst (Ω +e) ∅ˢ ] (∅ᴴ ⊩ᴿ R' [ τ ])
        inst' s = proj₁ (inst s) , fwd (proj₂ (inst s))

        opened : Search Q D
        opened = openˢ R' (λ τ h → sat τ (bwd h))

        readBack : (x : Maybe (Σ[ Q₀ ∈ Hyps (Ω +e) ] (Q₀ ⊩ᴿ bareᴿ R' [ idˢ ]))) → toHyps R' ≡ x
                 → Search Q D
        readBack nothing e with toHyps-nothing R' e
        ... | inj₁ (A , m , q) =
              refutedˢ (λ s → etDec-refute A q (proj₁ (inst' s)) (⊩ts (proj₂ (inst' s)) m))
        ... | inj₂ (A , B , m , q) with atomicᴸ m
        ...   | α , β , refl , refl = refutedˢ (λ _ → subDec-vars {Ω +e} α β q)
        readBack (just (Q₀ , hq)) e with checkClosed Q₀ in e'
        ... | nothing =
              refutedˢ (λ s → checkClosed-fail Q₀ e'
                                (proj₁ (inst' s) , ⊩ᴴ⇒⊨ (toHyps-compl R' e (proj₁ (inst' s)) (proj₂ (inst' s)))))
        ... | just _ with failingChain Q₀
        ...   | just n  =
                refutedˢ (λ s → n (proj₁ (inst' s) , ⊩ᴴ⇒⊨ (toHyps-compl R' e (proj₁ (inst' s)) (proj₂ (inst' s)))))
        ...   | nothing = opened

-- Matching on the deferred conditions first keeps the search unevaluated on
-- unknown ones

search : ∀ {Ω} → (Q : Hyps Ω) → (D : List (QOrd Ω)) → Search Q D
search Q []      = searchᴸ Q [] (localiseAll (asResid Q []))
search Q (E ∷ D) = searchᴸ Q (E ∷ D) (localiseAll (asResid Q (E ∷ D)))

------------------------------------------------------------------------
-- Closed decisions at a closed instance

-- An instance with the given values

setᵉ : ∀ {Ω} → EVar Ω → E → Subst Ω ∅ˢ → Subst Ω ∅ˢ
setᵉ k c τ = sub (sTy τ) (sR τ) (λ i → if ⌊ i ≟ᶠ k ⌋ then econst c else sE τ i)

setʳ : ∀ {Ω} → RVar Ω → R → Subst Ω ∅ˢ → Subst Ω ∅ˢ
setʳ k c τ = sub (sTy τ) (λ i → if ⌊ i ≟ᶠ k ⌋ then rconst c else sR τ i) (sE τ)

-- A deferred condition holds at a closed instance when its retry from no
-- hypotheses leaves nothing

dischargedAt : ∀ {Ω} → (τ : Subst Ω ∅ˢ) → (E : QOrd Ω) → Maybe (∅ᴴ ⊩ᴼ E [ τ ])
dischargedAt τ E with retryᵈ ∅ᴴ (E [ τ ]ᵠ)
... | keptᵈ [] b f = just (⊩ᴼ-resp-≐ˢ E (⨟-idʳ τ) (⊩ᴼ-subst E (b {Q = ∅ᴴ} idˢ ⊩ᴴ-∅ (λ ()))))
... | _            = nothing

decToMaybe : ∀ {X : Set} → Dec X → Maybe X
decToMaybe (yes p) = just p
decToMaybe (no _)  = nothing

-- Every atom of a residual decided at a closed instance

verify : ∀ {Ω} → (R : Resid Ω) → (τ : Subst Ω ∅ˢ) → Maybe (∅ᴴ ⊩ᴿ R [ τ ])
verify R τ
  with allOf {P = λ { (x , y) → ∅ᴴ ⊩ x [ τ ]ʳ ≾̂ᵣ y [ τ ]ʳ }}
             (λ { (x , y) → decToMaybe (x [ τ ]ʳ ≾̂ᵣ? y [ τ ]ʳ) }) (rs R)
     | allOf {P = λ { (x , y) → ∅ᴴ ⊩ x [ τ ]ᵉ ≾̂ₑ y [ τ ]ᵉ }}
             (λ { (x , y) → decToMaybe (x [ τ ]ᵉ ≾̂ₑ? y [ τ ]ᵉ) }) (es R)
     | allOf {P = λ A → ∅ᴴ ⊩Et A [ τ ]ᵛ} (λ A → decToMaybe (⊩Et? (A [ τ ]ᵛ))) (ts R)
     | allOf {P = λ { (A , B) → ∅ᴴ ⊩ A [ τ ]ᵛ <:̂ᵛ B [ τ ]ᵛ }}
             (λ { (A , B) → decToMaybe (A [ τ ]ᵛ <:̂ᵛ? B [ τ ]ᵛ) }) (ss R)
     | allOf {P = λ { (A , ρ) → ∅ᴴ ⊩ A [ τ ]ᵛ Et∨≾ᵘ ρ [ τ ]ʳ }}
             (λ { (A , ρ) → decToMaybe (Et∨≾ᵘ? (A [ τ ]ᵛ) (ρ [ τ ]ʳ)) }) (ds R)
     | allOf (dischargedAt τ) (dfs R)
... | just a | just b | just c | just d | just e | just f = just (mk⊩ᴿ a b c d e f)
... | _      | _      | _      | _      | _      | _      = nothing

------------------------------------------------------------------------
-- The items a closed instance must meet, and their classes

data Item (Ω : Scope) : Set where
  ordʳ : RExp Ω → RExp Ω → Item Ω
  ordᵉ : EExp Ω → EExp Ω → Item Ω
  cond : QOrd Ω → Item Ω

items : ∀ {Ω} → Resid Ω → List (Item Ω)
items R = map (λ { (x , y) → ordʳ x y }) (rs R) ++ map (λ { (x , y) → ordᵉ x y }) (es R)
          ++ map cond (dfs R)

unknownsOf : ∀ {Ω} → Item Ω → Vars Ω
unknownsOf (ordʳ x y) = fvʳ x ∪ᵛ fvʳ y
unknownsOf (ordᵉ x y) = fvᵉ x ∪ᵛ fvᵉ y
unknownsOf (cond E)   = fvᵈ E

holdsAt : ∀ {Ω} → Subst Ω ∅ˢ → Item Ω → 𝔹
holdsAt τ (ordʳ x y) = does (x [ τ ]ʳ ≾̂ᵣ? y [ τ ]ʳ)
holdsAt τ (ordᵉ x y) = does (x [ τ ]ᵉ ≾̂ₑ? y [ τ ]ᵉ)
holdsAt τ (cond E) with dischargedAt τ E
... | just _  = true
... | nothing = false

-- Whether two sets of grade unknowns meet, and whether one is empty

meets : ∀ {Ω} → Vars Ω → Vars Ω → 𝔹
meets V W = anyᶠ (λ i → vʳ V i ∧ vʳ W i) ∨ anyᶠ (λ i → vᵉ V i ∧ vᵉ W i)

noGrades : ∀ {Ω} → Vars Ω → 𝔹
noGrades V = not (anyᶠ (vʳ V) ∨ anyᶠ (vᵉ V))

-- The classes of items sharing unknowns, each item joining those it meets

Class : Scope → Set
Class Ω = Vars Ω × List (Item Ω)

join : ∀ {Ω} → Item Ω → List (Class Ω) → List (Class Ω)
join it cs = foldr merge (unknownsOf it , it ∷ []) (filterᵇ (λ c → meets (unknownsOf it) (proj₁ c)) cs)
           ∷ filterᵇ (λ c → not (meets (unknownsOf it) (proj₁ c))) cs
  where
    merge : Class _ → Class _ → Class _
    merge (V , is) (W , js) = V ∪ᵛ W , is ++ js

components : ∀ {Ω} → List (Item Ω) → List (Class Ω)
components = foldr join []

------------------------------------------------------------------------
-- Candidates

-- The occurrences of the marked unknowns in an expression

countₑ : ∀ {Ω} → (EVar Ω → 𝔹) → EExp Ω → ℕ
countₑ m (evar i)   = if m i then 1 else 0
countₑ m (econst _) = 0
countₑ m (a ·̂ₑ b)   = countₑ m a + countₑ m b
countₑ m (a ⊔̂ₑ b)   = countₑ m a + countₑ m b

countᵣ : ∀ {Ω} → (RVar Ω → 𝔹) → (EVar Ω → 𝔹) → RExp Ω → ℕ
countᵣ mr me (rvar i)   = if mr i then 1 else 0
countᵣ mr me (rconst _) = 0
countᵣ mr me (a ·̂ᵣ b)   = countᵣ mr me a + countᵣ mr me b
countᵣ mr me (a ⊔̂ᵣ b)   = countᵣ mr me a + countᵣ mr me b
countᵣ mr me ∣ ε ∣̂ᵉ     = countₑ me ε

-- The marks carried past the rigids of a condition, which are unmarked

liftᵉ : ∀ {Ω} → (k : ℕ) → (EVar Ω → 𝔹) → EVar (Ω +eⁿ k) → 𝔹
liftᵉ nzero        m = m
liftᵉ {Ω} (nsuc k) m = liftᵉ {Ω +e} k (λ { zero → false ; (suc i) → m i })

liftʳ : ∀ {Ω} → (k : ℕ) → (RVar Ω → 𝔹) → RVar (Ω +eⁿ k) → 𝔹
liftʳ nzero        m = m
liftʳ {Ω} (nsuc k) m = liftʳ {Ω +e} k m

maxOver : ∀ {X : Set} → (X → ℕ) → List X → ℕ
maxOver f = foldr (λ x n → f x ⊔ n) 0

-- The degree of an item in a set of unknowns: their most occurrences on one side

degreeOf : ∀ {Ω} → Vars Ω → Item Ω → ℕ
degreeOf V (ordʳ x y) = countᵣ (vʳ V) (vᵉ V) x ⊔ countᵣ (vʳ V) (vᵉ V) y
degreeOf V (ordᵉ x y) = countₑ (vᵉ V) x ⊔ countₑ (vᵉ V) y
degreeOf V (cond (qord _ k o)) =
  maxOver (λ { (x , y) → countᵣ mr me x ⊔ countᵣ mr me y }) (ors o)
  ⊔ maxOver (λ { (x , y) → countₑ me x ⊔ countₑ me y }) (oes o)
  where
    mr = liftʳ k (vʳ V)
    me = liftᵉ k (vᵉ V)

-- The constants of an item

constsOf : ∀ {Ω} → Item Ω → List R × List E
constsOf (ordʳ x y)         = constsᵣ x ++² constsᵣ y
constsOf (ordᵉ x y)         = [] , constsₑ x ++ constsₑ y
constsOf (cond (qord _ k o)) =
  foldr (λ { (x , y) c → (constsᵣ x ++² constsᵣ y) ++² c }) ([] , []) (ors o)
  ++² foldr (λ { (x , y) c → ([] , constsₑ x ++ constsₑ y) ++² c }) ([] , []) (oes o)

-- The candidates of a class

candsₑ : ℕ → List R × List E → List E
candsₑ d (rcs , ecs) = deduplicate _≃ₑ?_ (𝟏ₑ ∷ ⊤ₑ ∷ ecs ++ witnesses d rcs ecs)

candsᵣ : ℕ → List R × List E → List R
candsᵣ d (rcs , ecs) =
  deduplicate _≃ᵣ?_ (𝟏ᵣ ∷ ⊤ᵣ ∷ rcs ++ map ∣_∣ᵉ (ecs ++ witnesses d rcs ecs))

------------------------------------------------------------------------
-- The search of a class, and of a residual

-- Every assignment of candidates to the unknowns, from an instance

assignments : ∀ {Ω} → List E → List R → List (EVar Ω) → List (RVar Ω)
            → Subst Ω ∅ˢ → List (Subst Ω ∅ˢ)
assignments ce cr []       []       τ = τ ∷ []
assignments ce cr []       (k ∷ ks) τ = concatMap (λ c → assignments ce cr [] ks (setʳ k c τ)) cr
assignments ce cr (k ∷ ks) rs       τ = concatMap (λ c → assignments ce cr ks rs (setᵉ k c τ)) ce

firstWhere : ∀ {X : Set} → (X → 𝔹) → List X → Maybe X
firstWhere p []       = nothing
firstWhere p (x ∷ xs) = if p x then just x else firstWhere p xs

searchClass : ∀ {Ω} → Class Ω → Subst Ω ∅ˢ → Maybe (Subst Ω ∅ˢ)
searchClass {Ω} (V , is) τ =
  firstWhere (λ τ' → allHold τ' is)
    (assignments (candsₑ d cs) (candsᵣ d cs)
                 (filterᵇ (vᵉ V) (allFin (nE Ω))) (filterᵇ (vʳ V) (allFin (nR Ω))) τ)
  where
    d  = maxOver (degreeOf V) is
    cs = foldr (λ it c → constsOf it ++² c) ([] , []) is

    allHold : Subst Ω ∅ˢ → List (Item Ω) → 𝔹
    allHold τ' []        = true
    allHold τ' (it ∷ is') = holdsAt τ' it ∧ allHold τ' is'

searchAll : ∀ {Ω} → List (Class Ω) → Subst Ω ∅ˢ → Maybe (Subst Ω ∅ˢ)
searchAll []       τ = just τ
searchAll (c ∷ cs) τ with searchClass c τ
... | just τ' = searchAll cs τ'
... | nothing = nothing

------------------------------------------------------------------------
-- Establishment

data Establish {Ω} (Q : Hyps Ω) (D : List (QOrd Ω)) : Set where
  refutedᵉ   : ¬ Satisfiable (Q ++ᵠ D) → Establish Q D
  foundᵉ     : Satisfiable (Q ++ᵠ D) → Establish Q D
  undecidedᵉ : Establish Q D
  exhaustedᵉ : Establish Q D

-- From the outcome of the search

establishˢ : ∀ {Ω} {Q : Hyps Ω} {D : List (QOrd Ω)} → Search Q D → Establish Q D
establishˢ (refutedˢ n) = refutedᵉ n
establishˢ (openˢ R sat) with any (λ E → noGrades (fvᵈ E)) (dfs R)
... | true  = undecidedᵉ
... | false with searchAll (components (items R)) groundˢ
...   | nothing = exhaustedᵉ
...   | just τ with verify R τ
...     | just h  = foundᵉ (sat τ h)
...     | nothing = exhaustedᵉ

establish : ∀ {Ω} → (Q : Hyps Ω) → (D : List (QOrd Ω)) → Establish Q D
establish Q D = establishˢ (search Q D)
