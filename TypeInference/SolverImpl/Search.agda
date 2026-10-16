--------------------------------------------------------------------
-- The search for a closed instance of a solution                 --
--                                                                --
-- A solution's hypotheses and deferred conditions are read as a  --
-- residual (`asResid`) over the scope extended by one rigid that --
-- occurs nowhere, so that every unknown is local to it, and      --
-- `Localise.localise` gives the unknowns values (`localiseAll`). --
-- The deferred conditions are then retried from the orderings    --
-- left (`retry`), the atoms read back as hypotheses (`toHyps`),  --
-- and the closed check run, followed by the failing chains of    --
-- the whole graph, factor edges included (`checkClosed`,         --
-- `failingChain`). Each step can refute; otherwise the residual  --
-- left is open (`search`, `Search`).                             --
--                                                                --
-- Establishment (`establish`) goes on from an open residual. A   --
-- deferred condition left that mentions no unknown besides its   --
-- rigids is undecided. Otherwise each class of the orderings and --
-- deferred conditions sharing unknowns (`components`) is         --
-- searched in turn over every assignment of candidates to its    --
-- unknowns, the earlier classes' values kept: for an effect      --
-- unknown the unit, the top, the effect constants of the class   --
-- and the grade system's witnesses for its degree and constants; --
-- for a resource unknown the unit, the top, the resource         --
-- constants and the images of the effect candidates (`candsₑ`,   --
-- `candsᵣ`). An assignment is kept when every member of the      --
-- class holds at it, an ordering by the carrier's order, a       --
-- condition by its retry from no hypotheses. Each type unknown   --
-- is sent to the unit type. The instance assembled is verified   --
-- by the closed decisions of `Instances` (`verify`); exhausting  --
-- the candidates of a class leaves the residual unestablished.   --
--                                                                --
-- Contract. A refutation leaves the solution unsatisfiable       --
-- (`refutedˢ`): a closed instance of the solution enters the     --
-- scope, and localisation keeps it (`lcpl`), then at the unit    --
-- for the rigid it is a closed instance of the localised         --
-- residual, against which retry (`retry-fail`), the read-back    --
-- (`toHyps-compl`), the closed check (`checkClosed-fail`) and    --
-- the failing chains are each sound. A closed instance of an     --
-- open residual is one of the solution (`openˢ`), through the    --
-- localisation's values (`lsnd`) and the retry (`backᴰ`). An     --
-- instance found is verified, so establishment exhibits a closed --
-- instance of the solution (`foundᵉ`). Nothing is claimed of an  --
-- open residual, nor of an undecided or exhausted search.        --
--                                                                --
-- Backtracking search over a finite domain per unknown (Golomb   --
-- and Baumert, JACM 1965), one class of the constraint graph at  --
-- a time.                                                        --
--------------------------------------------------------------------

open import Data.Bool.Base using (true; false; _∨_; _∧_; not; if_then_else_) renaming (Bool to 𝔹)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap; foldr; allFin; filterᵇ;
                                  deduplicate)
open import Data.Bool.ListAction using (any)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ; _+_; _⊔_) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (does; ⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Search
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S
  using (Satisfiable; _≾̂ᵣ?_; _≾̂ₑ?_; ⊩ᴱ?; _<:̂ᵛ?_; VarOK?; _+eⁿ_)

open import TypeInference.SolverImpl.Deferred  S
  using (Dfr; dfr; _[_]ᵈ; _⊩ᵈ_[_]; ⊩ᵈ-resp-≐ˢ; ⊩ᵈ-subst; toOblig; ⊩ᴰ→⊩ᴼˢ; ⊩ᴼˢ→⊩ᴰ; κ⟨_⟩;
         Ords; ors; oes; allOf; constsₑ; constsᵣ; _++²_)
open import TypeInference.SolverImpl.Resid     S
open import TypeInference.SolverImpl.Entail    S using (checkClosed; checkClosed-fail; failingChain)
open import TypeInference.SolverImpl.Localise  S using (Localised; localise; lσ; lR; lsnd; lcpl; latom;
                                                         Entry; anyᶠ)
open import TypeInference.SolverImpl.Solve     S opEnum
  using (ordsOf; ordsOf-⊩; withDfs; retryᴰ; retryᵈ; retriedL; keptᵈ)
open import TypeInference.SolverImpl.Vars      S using (Vars; vʳ; vᵉ; _∪ᵛ_; fvʳ; fvᵉ)
open import TypeInference.SolverImpl.Strengthen S using (fvᵈ)

------------------------------------------------------------------------
-- A hypothesis set and deferred conditions as a residual

asResid : ∀ {Ψ} → Hyps Ψ → List (Dfr Ψ) → Resid Ψ
asResid Q D = resid (ordᵣ Q) (ordₑ Q) (map tvar (ets Q)) (map (mapᵖ tvar) (subᵥ Q)) (disj Q) D

asResid-⊩ : ∀ {Ψ Ψ'} {Q' : Hyps Ψ'} {Q : Hyps Ψ} {D : List (Dfr Ψ)} {δ : Subst Ψ Ψ'}
          → Q' ⊩ᴴ Q [ δ ] → (∀ {E} → E ∈ D → Q' ⊩ᵈ E [ δ ]) → Q' ⊩ᴿ asResid Q D [ δ ]
asResid-⊩ {Q' = Q'} {Q} {δ = δ} h g = mk⊩ᴿ (⊩ordᵣ h) (⊩ordₑ h) ts' ss' (⊩disj h) g
  where
    ts' : ∀ {A} → A ∈ map tvar (ets Q) → Q' ⊩ᴱ A [ δ ]ᵛ
    ts' m with ∈-map⁻ tvar m
    ... | α , m₀ , refl = ⊩ets h m₀

    ss' : ∀ {A B} → (A , B) ∈ map (mapᵖ tvar) (subᵥ Q) → Q' ∣ A [ δ ]ᵛ <:̂ᵛ B [ δ ]ᵛ
    ss' m with ∈-map⁻ (mapᵖ tvar) m
    ... | (α , β) , m₀ , refl = ⊩subᵥ h m₀

⊩-asResid : ∀ {Ψ Ψ'} {Q' : Hyps Ψ'} {Q : Hyps Ψ} {D : List (Dfr Ψ)} {δ : Subst Ψ Ψ'}
          → Q' ⊩ᴿ asResid Q D [ δ ] → Q' ⊩ᴴ Q [ δ ] × (∀ {E} → E ∈ D → Q' ⊩ᵈ E [ δ ])
⊩-asResid h =
  mk⊩ᴴ (λ m → ⊩ts h (∈-map⁺ tvar m)) (λ m → ⊩ss h (∈-map⁺ (mapᵖ tvar) m))
       (⊩rs h) (⊩es h) (⊩ds h) ,
  ⊩dfs h

asResid-atomic : ∀ {Ψ} {Q : Hyps Ψ} {D : List (Dfr Ψ)} → Atomicˢ (ss (asResid Q D))
asResid-atomic m with ∈-map⁻ (mapᵖ tvar) m
... | (α , β) , m₀ , refl = α , β , refl , refl

-- Weakening past an effect variable keeps subtyping demands atomic

atomic-wkᵉ : ∀ {Ψ} {l : List (OVType Ψ × OVType Ψ)} → Atomicˢ l
           → Atomicˢ (map (mapᵖ (_[ wkˢᵉ ]ᵛ)) l)
atomic-wkᵉ at m with ∈-map⁻ (mapᵖ (_[ wkˢᵉ ]ᵛ)) m
... | (A , B) , m₀ , refl with at m₀
...   | α , β , refl , refl = α , β , refl , refl

------------------------------------------------------------------------
-- Every unknown local
--
-- The scope is extended by one rigid, the only image of the scope's
-- entry; the residual, weakened past it, does not mention it.

rigid : ∀ {Ψ} → Subst (∅ˢ +e) (Ψ +e)
rigid = sub (λ ()) (λ ()) (λ { zero → evar zero })

localiseAll : ∀ {Ψ} → (R : Resid Ψ) → Localised (rigid {Ψ}) (R [ wkˢᵉ ]ᴿ)
localiseAll R = localise rigid (R [ wkˢᵉ ]ᴿ)

-- A closed instance, lifted past the rigid, enters the scope

entry : ∀ {Ψ} → (δ : Subst Ψ ∅ˢ) → Entry (rigid {Ψ}) (δ ↑ᵉ)
entry δ = idˢ , mk≐ˢ (λ ()) (λ ()) (λ { zero → refl })

-- and is a closed instance of the localised residual, the rigid sent to
-- the unit

closedᴸ : ∀ {Ψ} {R : Resid Ψ} → (L : Localised (rigid {Ψ}) (R [ wkˢᵉ ]ᴿ)) → (δ : Subst Ψ ∅ˢ)
        → ∅ᴴ ⊩ᴿ R [ δ ] → ∅ᴴ ⊩ᴿ lR L [ δ ↑ᵉ ⨟ˢ κ⟨ ûₑ ⟩ ]
closedᴸ L δ h =
  ⊩ᴿ-⨟ ⊩ᴴ-∅
    (lcpl L (δ ↑ᵉ) (entry δ)
      (⊩ᴿ-subst⁻ (⊩ᴿ-resp-≐ˢ (≐ˢ-sym (wkˢᵉ-↑ᵉ δ)) (⊩ᴿ-⨟ ⊩ᴴ-∅ h))))

-- A closed instance of the localised residual is one of the residual,
-- through the values

openᴸ : ∀ {Ψ} {R : Resid Ψ} → (L : Localised (rigid {Ψ}) (R [ wkˢᵉ ]ᴿ))
      → (τ : Subst (Ψ +e) ∅ˢ) → ∅ᴴ ⊩ᴿ lR L [ τ ] → ∅ᴴ ⊩ᴿ R [ wkˢᵉ ⨟ˢ (lσ L ⨟ˢ τ) ]
openᴸ L τ h = ⊩ᴿ-subst (lsnd L τ ∅ᴴ h)

------------------------------------------------------------------------
-- The search

data Search {Ψ} (Q : Hyps Ψ) (D : List (Dfr Ψ)) : Set where
  refutedˢ : ¬ Satisfiable Q (map toOblig D) → Search Q D
  openˢ    : (R : Resid (Ψ +e))
           → ((τ : Subst (Ψ +e) ∅ˢ) → ∅ᴴ ⊩ᴿ R [ τ ] → Satisfiable Q (map toOblig D))
           → Search Q D

-- A subtyping demand between type variables always reads back

subDec-vars : ∀ {Ψ} → (α β : TyVar Ψ) → subDec {Ψ} (tvar α) (tvar β) ≡ nothing → ⊥
subDec-vars α β ()

-- The search from a localisation of the solution's residual

searchᴸ : ∀ {Ψ} → (Q : Hyps Ψ) → (D : List (Dfr Ψ))
        → Localised (rigid {Ψ}) (asResid Q D [ wkˢᵉ ]ᴿ) → Search Q D
searchᴸ {Ψ} Q D L = retried (retryᴰ (ordsOf (lR L)) (dfs (lR L)))
  where
    -- a closed instance of the solution, of the localised residual

    inst : Satisfiable Q (map toOblig D) → Σ[ τ ∈ Subst (Ψ +e) ∅ˢ ] (∅ᴴ ⊩ᴿ lR L [ τ ])
    inst (δ , hQ ∷ hD) = δ ↑ᵉ ⨟ˢ κ⟨ ûₑ ⟩ , closedᴸ L δ (asResid-⊩ hQ (⊩ᴼˢ→⊩ᴰ {Q = ∅ᴴ} {δ = δ} D hD))

    -- and back

    sat : (τ : Subst (Ψ +e) ∅ˢ) → ∅ᴴ ⊩ᴿ lR L [ τ ] → Satisfiable Q (map toOblig D)
    sat τ h = wkˢᵉ ⨟ˢ (lσ L ⨟ˢ τ) , proj₁ hs ∷ ⊩ᴰ→⊩ᴼˢ {Q = ∅ᴴ} {δ = wkˢᵉ ⨟ˢ (lσ L ⨟ˢ τ)} D (proj₂ hs)
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

        inst' : Satisfiable Q (map toOblig D) → Σ[ τ ∈ Subst (Ψ +e) ∅ˢ ] (∅ᴴ ⊩ᴿ R' [ τ ])
        inst' s = proj₁ (inst s) , fwd (proj₂ (inst s))

        opened : Search Q D
        opened = openˢ R' (λ τ h → sat τ (bwd h))

        readBack : (x : Maybe (Σ[ Q₀ ∈ Hyps (Ψ +e) ] (Q₀ ⊩ᴿ bareᴿ R' [ idˢ ]))) → toHyps R' ≡ x
                 → Search Q D
        readBack nothing e with toHyps-nothing R' e
        ... | inj₁ (A , m , q) =
              refutedˢ (λ s → etDec-refute A q (proj₁ (inst' s)) (⊩ts (proj₂ (inst' s)) m))
        ... | inj₂ (A , B , m , q) with atomicᴸ m
        ...   | α , β , refl , refl = refutedˢ (λ _ → subDec-vars {Ψ +e} α β q)
        readBack (just (Q₀ , hq)) e with checkClosed Q₀ in e'
        ... | nothing =
              refutedˢ (λ s → checkClosed-fail Q₀ e'
                                (proj₁ (inst' s) , toHyps-compl R' e (proj₁ (inst' s)) (proj₂ (inst' s)) ∷ []))
        ... | just _ with failingChain Q₀
        ...   | just n  =
                refutedˢ (λ s → n (proj₁ (inst' s) , toHyps-compl R' e (proj₁ (inst' s)) (proj₂ (inst' s)) ∷ []))
        ...   | nothing = opened

-- Matching on the deferred conditions first leaves the search
-- unevaluated on unknown ones.

search : ∀ {Ψ} → (Q : Hyps Ψ) → (D : List (Dfr Ψ)) → Search Q D
search Q []      = searchᴸ Q [] (localiseAll (asResid Q []))
search Q (E ∷ D) = searchᴸ Q (E ∷ D) (localiseAll (asResid Q (E ∷ D)))

------------------------------------------------------------------------
-- Closed decisions at a closed instance

-- An instance with the given values

setᵉ : ∀ {Ψ} → EVar Ψ → E → Subst Ψ ∅ˢ → Subst Ψ ∅ˢ
setᵉ k c τ = sub (sTy τ) (sR τ) (λ i → if ⌊ i ≟ᶠ k ⌋ then econst c else sE τ i)

setʳ : ∀ {Ψ} → RVar Ψ → R → Subst Ψ ∅ˢ → Subst Ψ ∅ˢ
setʳ k c τ = sub (sTy τ) (λ i → if ⌊ i ≟ᶠ k ⌋ then rconst c else sR τ i) (sE τ)

-- A deferred condition holds at a closed instance when its retry from
-- no hypotheses leaves nothing

dischargedAt : ∀ {Ψ} → (τ : Subst Ψ ∅ˢ) → (E : Dfr Ψ) → Maybe (∅ᴴ ⊩ᵈ E [ τ ])
dischargedAt τ E with retryᵈ ∅ᴴ (E [ τ ]ᵈ)
... | keptᵈ [] b f = just (⊩ᵈ-resp-≐ˢ E (⨟-idʳ τ) (⊩ᵈ-subst E (b idˢ ⊩ᴴ-∅ (λ ()))))
... | _            = nothing

decToMaybe : ∀ {X : Set} → Dec X → Maybe X
decToMaybe (yes p) = just p
decToMaybe (no _)  = nothing

-- Every atom of a residual decided at a closed instance

verify : ∀ {Ψ} → (R : Resid Ψ) → (τ : Subst Ψ ∅ˢ) → Maybe (∅ᴴ ⊩ᴿ R [ τ ])
verify R τ
  with allOf {P = λ { (x , y) → ∅ᴴ ⊩ x [ τ ]ʳ ≾̂ᵣ y [ τ ]ʳ }}
             (λ { (x , y) → decToMaybe (x [ τ ]ʳ ≾̂ᵣ? y [ τ ]ʳ) }) (rs R)
     | allOf {P = λ { (x , y) → ∅ᴴ ⊩ x [ τ ]ᵉ ≾̂ₑ y [ τ ]ᵉ }}
             (λ { (x , y) → decToMaybe (x [ τ ]ᵉ ≾̂ₑ? y [ τ ]ᵉ) }) (es R)
     | allOf {P = λ A → ∅ᴴ ⊩ᴱ A [ τ ]ᵛ} (λ A → decToMaybe (⊩ᴱ? (A [ τ ]ᵛ))) (ts R)
     | allOf {P = λ { (A , B) → ∅ᴴ ∣ A [ τ ]ᵛ <:̂ᵛ B [ τ ]ᵛ }}
             (λ { (A , B) → decToMaybe (A [ τ ]ᵛ <:̂ᵛ? B [ τ ]ᵛ) }) (ss R)
     | allOf {P = λ { (A , ρ) → VarOK ∅ᴴ (A [ τ ]ᵛ) (ρ [ τ ]ʳ) }}
             (λ { (A , ρ) → decToMaybe (VarOK? (A [ τ ]ᵛ) (ρ [ τ ]ʳ)) }) (ds R)
     | allOf (dischargedAt τ) (dfs R)
... | just a | just b | just c | just d | just e | just f = just (mk⊩ᴿ a b c d e f)
... | _      | _      | _      | _      | _      | _      = nothing

------------------------------------------------------------------------
-- The items a closed instance must meet, and their classes

data Item (Ψ : Scope) : Set where
  ordʳ : RExp Ψ → RExp Ψ → Item Ψ
  ordᵉ : EExp Ψ → EExp Ψ → Item Ψ
  cond : Dfr Ψ → Item Ψ

items : ∀ {Ψ} → Resid Ψ → List (Item Ψ)
items R = map (λ { (x , y) → ordʳ x y }) (rs R) ++ map (λ { (x , y) → ordᵉ x y }) (es R)
          ++ map cond (dfs R)

unknownsOf : ∀ {Ψ} → Item Ψ → Vars Ψ
unknownsOf (ordʳ x y) = fvʳ x ∪ᵛ fvʳ y
unknownsOf (ordᵉ x y) = fvᵉ x ∪ᵛ fvᵉ y
unknownsOf (cond E)   = fvᵈ E

holdsAt : ∀ {Ψ} → Subst Ψ ∅ˢ → Item Ψ → 𝔹
holdsAt τ (ordʳ x y) = does (x [ τ ]ʳ ≾̂ᵣ? y [ τ ]ʳ)
holdsAt τ (ordᵉ x y) = does (x [ τ ]ᵉ ≾̂ₑ? y [ τ ]ᵉ)
holdsAt τ (cond E) with dischargedAt τ E
... | just _  = true
... | nothing = false

-- Whether two sets of grade unknowns meet, and whether one is empty

meets : ∀ {Ψ} → Vars Ψ → Vars Ψ → 𝔹
meets V W = anyᶠ (λ i → vʳ V i ∧ vʳ W i) ∨ anyᶠ (λ i → vᵉ V i ∧ vᵉ W i)

noGrades : ∀ {Ψ} → Vars Ψ → 𝔹
noGrades V = not (anyᶠ (vʳ V) ∨ anyᶠ (vᵉ V))

-- The classes of items sharing unknowns: each item joins the classes it
-- meets

Class : Scope → Set
Class Ψ = Vars Ψ × List (Item Ψ)

join : ∀ {Ψ} → Item Ψ → List (Class Ψ) → List (Class Ψ)
join it cs = foldr merge (unknownsOf it , it ∷ []) (filterᵇ (λ c → meets (unknownsOf it) (proj₁ c)) cs)
           ∷ filterᵇ (λ c → not (meets (unknownsOf it) (proj₁ c))) cs
  where
    merge : Class _ → Class _ → Class _
    merge (V , is) (W , js) = V ∪ᵛ W , is ++ js

components : ∀ {Ψ} → List (Item Ψ) → List (Class Ψ)
components = foldr join []

------------------------------------------------------------------------
-- Candidates

-- The occurrences of the marked unknowns in an expression

countₑ : ∀ {Ψ} → (EVar Ψ → 𝔹) → EExp Ψ → ℕ
countₑ m (evar i)   = if m i then 1 else 0
countₑ m (econst _) = 0
countₑ m (a ·̂ₑ b)   = countₑ m a + countₑ m b
countₑ m (a ⊔̂ₑ b)   = countₑ m a + countₑ m b

countᵣ : ∀ {Ψ} → (RVar Ψ → 𝔹) → (EVar Ψ → 𝔹) → RExp Ψ → ℕ
countᵣ mr me (rvar i)   = if mr i then 1 else 0
countᵣ mr me (rconst _) = 0
countᵣ mr me (a ·̂ᵣ b)   = countᵣ mr me a + countᵣ mr me b
countᵣ mr me (a ⊔̂ᵣ b)   = countᵣ mr me a + countᵣ mr me b
countᵣ mr me ∣ ε ∣̂ᵉ     = countₑ me ε

-- The marks carried past the rigids of a condition, which are unmarked

liftᵉ : ∀ {Ψ} → (k : ℕ) → (EVar Ψ → 𝔹) → EVar (Ψ +eⁿ k) → 𝔹
liftᵉ nzero        m = m
liftᵉ {Ψ} (nsuc k) m = liftᵉ {Ψ +e} k (λ { zero → false ; (suc i) → m i })

liftʳ : ∀ {Ψ} → (k : ℕ) → (RVar Ψ → 𝔹) → RVar (Ψ +eⁿ k) → 𝔹
liftʳ nzero        m = m
liftʳ {Ψ} (nsuc k) m = liftʳ {Ψ +e} k m

maxOver : ∀ {X : Set} → (X → ℕ) → List X → ℕ
maxOver f = foldr (λ x n → f x ⊔ n) 0

-- The degree of an item in a set of unknowns: their most occurrences on
-- one side of an ordering

degreeOf : ∀ {Ψ} → Vars Ψ → Item Ψ → ℕ
degreeOf V (ordʳ x y) = countᵣ (vʳ V) (vᵉ V) x ⊔ countᵣ (vʳ V) (vᵉ V) y
degreeOf V (ordᵉ x y) = countₑ (vᵉ V) x ⊔ countₑ (vᵉ V) y
degreeOf V (cond (dfr _ k o)) =
  maxOver (λ { (x , y) → countᵣ mr me x ⊔ countᵣ mr me y }) (ors o)
  ⊔ maxOver (λ { (x , y) → countₑ me x ⊔ countₑ me y }) (oes o)
  where
    mr = liftʳ k (vʳ V)
    me = liftᵉ k (vᵉ V)

-- The constants of an item

constsOf : ∀ {Ψ} → Item Ψ → List R × List E
constsOf (ordʳ x y)         = constsᵣ x ++² constsᵣ y
constsOf (ordᵉ x y)         = [] , constsₑ x ++ constsₑ y
constsOf (cond (dfr _ k o)) =
  foldr (λ { (x , y) c → (constsᵣ x ++² constsᵣ y) ++² c }) ([] , []) (ors o)
  ++² foldr (λ { (x , y) c → ([] , constsₑ x ++ constsₑ y) ++² c }) ([] , []) (oes o)

-- The candidates of a class

candsₑ : ℕ → List R × List E → List E
candsₑ d (rcs , ecs) = deduplicate _≡ₑ?_ (uₑ ∷ ⊤ₑ ∷ ecs ++ witnesses d rcs ecs)

candsᵣ : ℕ → List R × List E → List R
candsᵣ d (rcs , ecs) =
  deduplicate _≡ᵣ?_ (uᵣ ∷ ⊤ᵣ ∷ rcs ++ map mapᵉ (ecs ++ witnesses d rcs ecs))

------------------------------------------------------------------------
-- The search of a class, and of a residual

-- Every assignment of candidates to the unknowns, from an instance

assignments : ∀ {Ψ} → List E → List R → List (EVar Ψ) → List (RVar Ψ)
            → Subst Ψ ∅ˢ → List (Subst Ψ ∅ˢ)
assignments ce cr []       []       τ = τ ∷ []
assignments ce cr []       (k ∷ ks) τ = concatMap (λ c → assignments ce cr [] ks (setʳ k c τ)) cr
assignments ce cr (k ∷ ks) rs       τ = concatMap (λ c → assignments ce cr ks rs (setᵉ k c τ)) ce

firstWhere : ∀ {X : Set} → (X → 𝔹) → List X → Maybe X
firstWhere p []       = nothing
firstWhere p (x ∷ xs) = if p x then just x else firstWhere p xs

searchClass : ∀ {Ψ} → Class Ψ → Subst Ψ ∅ˢ → Maybe (Subst Ψ ∅ˢ)
searchClass {Ψ} (V , is) τ =
  firstWhere (λ τ' → allHold τ' is)
    (assignments (candsₑ d cs) (candsᵣ d cs)
                 (filterᵇ (vᵉ V) (allFin (nE Ψ))) (filterᵇ (vʳ V) (allFin (nR Ψ))) τ)
  where
    d  = maxOver (degreeOf V) is
    cs = foldr (λ it c → constsOf it ++² c) ([] , []) is

    allHold : Subst Ψ ∅ˢ → List (Item Ψ) → 𝔹
    allHold τ' []        = true
    allHold τ' (it ∷ is') = holdsAt τ' it ∧ allHold τ' is'

searchAll : ∀ {Ψ} → List (Class Ψ) → Subst Ψ ∅ˢ → Maybe (Subst Ψ ∅ˢ)
searchAll []       τ = just τ
searchAll (c ∷ cs) τ with searchClass c τ
... | just τ' = searchAll cs τ'
... | nothing = nothing

------------------------------------------------------------------------
-- Establishment

data Establish {Ψ} (Q : Hyps Ψ) (D : List (Dfr Ψ)) : Set where
  refutedᵉ   : ¬ Satisfiable Q (map toOblig D) → Establish Q D
  foundᵉ     : Satisfiable Q (map toOblig D) → Establish Q D
  undecidedᵉ : Establish Q D
  exhaustedᵉ : Establish Q D

-- From the outcome of the search

establishˢ : ∀ {Ψ} {Q : Hyps Ψ} {D : List (Dfr Ψ)} → Search Q D → Establish Q D
establishˢ (refutedˢ n) = refutedᵉ n
establishˢ (openˢ R sat) with any (λ E → noGrades (fvᵈ E)) (dfs R)
... | true  = undecidedᵉ
... | false with searchAll (components (items R)) groundˢ
...   | nothing = exhaustedᵉ
...   | just τ with verify R τ
...     | just h  = foundᵉ (sat τ h)
...     | nothing = exhaustedᵉ

establish : ∀ {Ψ} → (Q : Hyps Ψ) → (D : List (Dfr Ψ)) → Establish Q D
establish Q D = establishˢ (search Q D)
