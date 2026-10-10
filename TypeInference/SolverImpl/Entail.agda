--------------------------------------------------------------------
-- Entailment of grade orderings from hypotheses                  --
--                                                                --
-- The hypothesis graph of a set `Q` has the grade expressions of --
-- a sort as vertices. Its edges (`Edgeₑ`, `Edgeᵣ`) are the       --
-- orderings of `Q` (`hyp`), the grade's order between constants  --
-- (`cst`), the links to the top (`top`) and from the unit when   --
-- the grade declares it least (`unit`), and on the resource side --
-- the images of the effect edges (`img`).                        --
--                                                                --
-- A query `e ≾ e'` is answered at an explicit strength           --
-- (`Strength`, `decideₑ`, `decideᵣ`):                             --
--   * `closed`: both sides variable-free, compared by the        --
--     grade's `_≾?_` (`closedₑ?`, `closedᵣ?`);                   --
--   * `derive`: the embedding of normal forms of `Normal`, its   --
--     atoms compared by identity, along the links and along      --
--     chains of the edges between single atoms;                  --
--   * `atomic`: an ordering of `Q` itself, or `derive`.          --
-- `refute≾u` refutes `ρ ≾ u` at every instance by the            --
-- zero-product law, and `checkClosed` decides the closed atoms   --
-- of `Q` and the closed orderings joined by a chain of `hyp`     --
-- edges.                                                         --
--                                                                --
-- Contract. Every edge holds where `Q` does (`edgeₑ-sound`,      --
-- `edgeᵣ-sound`; at an instance by `⊩-substₑ`/`⊩-substᵣ`).        --
-- Each decision is sound by its type: a `just` is a derivation   --
-- of `Q ⊩ e ≾̂ e'` composed of edges by the laws. A `nothing`     --
-- claims nothing; no completeness is proved. `refute≾u` is sound --
-- by its type (`Refutedᵤ`), stable under instantiation           --
-- (`refute-[]ʳ`), and rules out `ρ ≾ u` from every satisfiable   --
-- set (`refute-⊩`). `checkClosed Q` entails `Q`                  --
-- (`checkClosed-⊩`), is entailed wherever `Q` is                 --
-- (`checkClosed-⊆`), and a failure leaves `Q` unsatisfiable      --
-- (`checkClosed-fail`).                                          --
--------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.Bool.ListAction using (any)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁻; ∈-map⁻)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (lookup-result)
open import Data.Maybe.Base using (Maybe; just; nothing; is-just; _<∣>_)
open import Data.Maybe using (Is-just; to-witness)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)

open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  using () renaming (ε to ◅-nil; _◅_ to _◅◅_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (does)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Entail (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S
  using (Satisfiable; VarOK-∅; valʳ; inst-≡̂ᵣ; inst-≾ᵣ; val-≾ᵣ⁻; closed-≾ᵣ; closed-≾ₑ)

open import TypeInference.SolverImpl.Normal S
open import TypeInference.SolverImpl.Resid  S using (etDec; etDec-refute)
import TypeInference.SolverImpl.Reach as Reachability

------------------------------------------------------------------------
-- The hypothesis graph

data Edgeₑ {Θ : Scope} (Q : Hyps Θ) : EExp Θ → EExp Θ → Set where
  hyp  : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → Edgeₑ Q ε ε'
  cst  : ∀ {c c'} → c ≾ₑ c' → Edgeₑ Q (econst c) (econst c')
  top  : ∀ {ε} → Edgeₑ Q ε (econst ⊤ₑ)
  unit : ∀ {ε} → Is-just uₑ-least? → Edgeₑ Q ûₑ ε

data Edgeᵣ {Θ : Scope} (Q : Hyps Θ) : RExp Θ → RExp Θ → Set where
  hyp  : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → Edgeᵣ Q ρ ρ'
  cst  : ∀ {c c'} → c ≾ᵣ c' → Edgeᵣ Q (rconst c) (rconst c')
  top  : ∀ {ρ} → Edgeᵣ Q ρ (rconst ⊤ᵣ)
  unit : ∀ {ρ} → Is-just uᵣ-least? → Edgeᵣ Q ûᵣ ρ
  img  : ∀ {ε ε'} → Edgeₑ Q ε ε' → Edgeᵣ Q ∣ ε ∣̂ᵉ ∣ ε' ∣̂ᵉ

-- Every edge holds where the hypotheses do

edgeₑ-sound : ∀ {Θ} {Q : Hyps Θ} {ε ε'} → Edgeₑ Q ε ε' → Q ⊩ ε ≾̂ₑ ε'
edgeₑ-sound (hyp m)  = hypₑ m
edgeₑ-sound (cst p)  = atomₑ p
edgeₑ-sound top      = topₑ
edgeₑ-sound (unit q) = minₑ q

edgeᵣ-sound : ∀ {Θ} {Q : Hyps Θ} {ρ ρ'} → Edgeᵣ Q ρ ρ' → Q ⊩ ρ ≾̂ᵣ ρ'
edgeᵣ-sound (hyp m)  = hypᵣ m
edgeᵣ-sound (cst p)  = atomᵣ p
edgeᵣ-sound top      = topᵣ
edgeᵣ-sound (unit q) = minᵣ q
edgeᵣ-sound (img e)  = map-mono (edgeₑ-sound e)

------------------------------------------------------------------------
-- Factor edges
--
-- The graph has no edge from a factor to a product, `a ≾ a · b` where
-- the unit is below `b`.

------------------------------------------------------------------------
-- Links and the edges between single atoms
--
-- Two atoms are linked when they are equal, or are constants joined
-- by a `cst` edge. The edges between atoms are the `hyp` edges whose
-- two sides are single atoms and, on the resource side, the images of
-- the effect ones, each read as an entailment.

EEdge : ∀ {Θ} → Hyps Θ → Set
EEdge {Θ} Q = Σ[ a ∈ EAtom Θ ] Σ[ b ∈ EAtom Θ ] (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)

REdge : ∀ {Θ} → Hyps Θ → Set
REdge {Θ} Q = Σ[ a ∈ RAtom Θ ] Σ[ b ∈ RAtom Θ ] (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)

AEdgeₑ : ∀ {Θ} → Hyps Θ → Set
AEdgeₑ {Θ} Q = Σ[ a ∈ EAtom Θ ] Σ[ b ∈ EAtom Θ ] Edgeₑ Q ⟦ a ⟧ᵉᵃ ⟦ b ⟧ᵉᵃ

AEdgeᵣ : ∀ {Θ} → Hyps Θ → Set
AEdgeᵣ {Θ} Q = Σ[ a ∈ RAtom Θ ] Σ[ b ∈ RAtom Θ ] Edgeᵣ Q ⟦ a ⟧ʳᵃ ⟦ b ⟧ʳᵃ

atomicₑ : ∀ {Θ} {Q : Hyps Θ} → (l : List (EExp Θ × EExp Θ))
        → (∀ {p} → p ∈ l → p ∈ ordₑ Q) → List (AEdgeₑ Q)
atomicₑ []             k = []
atomicₑ ((ε , ε') ∷ l) k with atomᵉ? ε | atomᵉ? ε'
... | just (a , refl) | just (b , refl) = (a , b , hyp (k (here refl))) ∷ atomicₑ l (λ m → k (there m))
... | _               | _               = atomicₑ l (λ m → k (there m))

atomicᵣ : ∀ {Θ} {Q : Hyps Θ} → (l : List (RExp Θ × RExp Θ))
        → (∀ {p} → p ∈ l → p ∈ ordᵣ Q) → List (AEdgeᵣ Q)
atomicᵣ []             k = []
atomicᵣ ((ρ , ρ') ∷ l) k with atomʳ? ρ | atomʳ? ρ'
... | just (a , refl) | just (b , refl) = (a , b , hyp (k (here refl))) ∷ atomicᵣ l (λ m → k (there m))
... | _               | _               = atomicᵣ l (λ m → k (there m))

readₑ : ∀ {Θ} {Q : Hyps Θ} → AEdgeₑ Q → EEdge Q
readₑ (a , b , e) = a , b , edgeₑ-sound e

readᵣ : ∀ {Θ} {Q : Hyps Θ} → AEdgeᵣ Q → REdge Q
readᵣ (a , b , e) = a , b , edgeᵣ-sound e

-- The image of an edge between effect atoms, between their images

imageᵣ : ∀ {Θ} {Q : Hyps Θ} → AEdgeₑ Q → REdge Q
imageᵣ (a , b , e) =
  ∣ a ∣ᵃ , ∣ b ∣ᵃ , transᵣ (eqᵣ (≡̂ᵣ-sym ∣⟦ a ⟧∣)) (transᵣ (edgeᵣ-sound (img e)) (eqᵣ ∣⟦ b ⟧∣))

edgesₑ : ∀ {Θ} → (Q : Hyps Θ) → List (EEdge Q)
edgesₑ Q = map readₑ (atomicₑ (ordₑ Q) (λ m → m))

edgesᵣ : ∀ {Θ} → (Q : Hyps Θ) → List (REdge Q)
edgesᵣ Q = map readᵣ (atomicᵣ (ordᵣ Q) (λ m → m)) ++ map imageᵣ (atomicₑ (ordₑ Q) (λ m → m))

linkₑ? : ∀ {Θ} {Q : Hyps Θ} → (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
linkₑ? (ac c) (ac d) with c ≾ₑ? d
... | yes p = just (edgeₑ-sound (cst p))
... | no _  = nothing
linkₑ? (av i) (av j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ₑ-refl
... | no _     = nothing
linkₑ? _      _      = nothing

linkᵣ? : ∀ {Θ} {Q : Hyps Θ} → (a b : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
linkᵣ? (rc c) (rc d) with c ≾ᵣ? d
... | yes p = just (edgeᵣ-sound (cst p))
... | no _  = nothing
linkᵣ? (rv i) (rv j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ᵣ-refl
... | no _     = nothing
linkᵣ? (rm i) (rm j) with i ≟ᶠ j
... | yes refl = just ⊩≾̂ᵣ-refl
... | no _     = nothing
linkᵣ? _      _      = nothing

-- What the sources of the edges between atoms reach

tableₑ : ∀ {Θ} → (Q : Hyps Θ) → Chains.Table (λ a b → Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
                                              ⊩≾̂ₑ-refl transₑ linkₑ? _≟ᵃₑ_ (edgesₑ Q)
tableₑ Q = Chains.table _ ⊩≾̂ₑ-refl transₑ linkₑ? _≟ᵃₑ_ (edgesₑ Q)

tableᵣ : ∀ {Θ} → (Q : Hyps Θ) → Chains.Table (λ a b → Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
                                              ⊩≾̂ᵣ-refl transᵣ linkᵣ? _≟ᵃᵣ_ (edgesᵣ Q)
tableᵣ Q = Chains.table _ ⊩≾̂ᵣ-refl transᵣ linkᵣ? _≟ᵃᵣ_ (edgesᵣ Q)

-- The unit below anything, along a `unit` edge

min≾ₑ : ∀ {Θ} {Q : Hyps Θ} {ε : EExp Θ} → Maybe (Is-just uₑ-least?) → Maybe (Q ⊩ ûₑ ≾̂ₑ ε)
min≾ₑ (just q) = just (edgeₑ-sound (unit q))
min≾ₑ nothing  = nothing

min≾ᵣ : ∀ {Θ} {Q : Hyps Θ} {ρ : RExp Θ} → Maybe (Is-just uᵣ-least?) → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ρ)
min≾ᵣ (just q) = just (edgeᵣ-sound (unit q))
min≾ᵣ nothing  = nothing

------------------------------------------------------------------------
-- The strength `derive`: the embedding of `Normal` along the chains
-- of the edges between atoms
--
-- Both sides are compared alternative by alternative: `⊔-lub`
-- reduces the left side to each of its alternatives in turn, and
-- `⊔-ubˡ`/`⊔-ubʳ` pick out an alternative of the right side for each.
-- The right side is first grouped by skeleton, and each group that
-- varies in one slot folded into one alternative, that slot holding
-- the join of its constants (`foldSumₑ`/`foldSumᵣ`). Two atoms are
-- compared by a link, by a `top` edge to an atom the top reaches,
-- and along the chains; the unit is below an atom along a `unit`
-- edge or a chain from the constant `u`.

module Searchₑ {Θ} {Q : Hyps Θ}
               (t : Chains.Table (λ a b → Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
                                 ⊩≾̂ₑ-refl transₑ linkₑ? _≟ᵃₑ_ (edgesₑ Q)) where

  reachₑ? : (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  reachₑ? = Chains.reach? _ ⊩≾̂ₑ-refl transₑ linkₑ? _≟ᵃₑ_ (edgesₑ Q) t

  -- Anything is below an atom that the top reaches

  ceilₑ : ∀ {ε : EExp Θ} → (b : EAtom Θ) → Maybe (Q ⊩ ε ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  ceilₑ b with reachₑ? (ac ⊤ₑ) b
  ... | just p  = just (transₑ (edgeₑ-sound top) p)
  ... | nothing = nothing

  -- An atom below an atom: linked, below an atom above the top, or
  -- reached along the atomic hypotheses

  atom≾ₑ : (a b : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  atom≾ₑ a b = linkₑ? a b <∣> ceilₑ b <∣> reachₑ? a b

  -- The unit below an atom: when the grade's unit is least, or as the
  -- constant atom `uₑ`

  unit≾ₑ : (b : EAtom Θ) → Maybe (Q ⊩ ûₑ ≾̂ₑ ⟦ b ⟧ᵉᵃ)
  unit≾ₑ b = min≾ₑ (Is-just? uₑ-least?) <∣> atom≾ₑ (ac uₑ) b

  -- An atom below the unit, as the constant atom `uₑ`

  ≾unitₑ : (a : EAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ᵉᵃ ≾̂ₑ ûₑ)
  ≾unitₑ a = atom≾ₑ a (ac uₑ)

  -- The product comparison, its atom comparisons being these

  constᵉ? : EAtom Θ → Maybe E
  constᵉ? (ac c) = just c
  constᵉ? (av _) = nothing

  module Pₑ = Embedding constᵉ? (λ c → consₑ (ac c)) consₑ-length
                (λ a b → Is-just (atom≾ₑ a b)) (λ a b → is-just? (atom≾ₑ a b))
                (λ b → Is-just (unit≾ₑ b))     (λ b → is-just? (unit≾ₑ b))
                (λ a → Is-just (≾unitₑ a))     (λ a → is-just? (≾unitₑ a))
                (λ b → Is-just (reachₑ? (ac ⊤ₑ) b)) (λ b → is-just? (reachₑ? (ac ⊤ₑ) b))
                (Is-just ·ₑ-comm?) (is-just? ·ₑ-comm?)
  open Pₑ using (Step; match; skipʳ; skipˡ; absorb; mergeʳ; mergeˡ; pick; absorbAt)

  -- Each step is an entailment, one use of `monoₑ` on products read
  -- back with a trailing unit (`⟦_⟧ᵉˢ`)

  stepₑ : ∀ {as bs as' bs'} → Step as bs as' bs'
        → Q ⊩ ⟦ as' ⟧ᵉˢ ≾̂ₑ ⟦ bs' ⟧ᵉˢ → Q ⊩ ⟦ as ⟧ᵉˢ ≾̂ₑ ⟦ bs ⟧ᵉˢ
  stepₑ (match p)  q = monoₑ (to-witness p) q
  stepₑ (skipʳ p)  q = transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityˡ)) (monoₑ (to-witness p) q)
  stepₑ (skipˡ p)  q = transₑ (monoₑ (to-witness p) q) (eqₑ ≡̂ₑ-identityˡ)
  stepₑ (absorb p) q =
    transₑ (monoₑ ⊩≾̂ₑ-refl q)
           (transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-assoc)) (monoₑ (transₑ (edgeₑ-sound top) (to-witness p)) ⊩≾̂ₑ-refl))
  stepₑ (mergeʳ {a = ac c} {bs = bs} refl p) q =
    transₑ q (transₑ (eqₑ (≡̂ₑ-trans (consₑ-≡ (ac c) bs)
                                    (≡̂ₑ-cong ≡̂ₑ-refl (≡̂ₑ-sym ≡̂ₑ-identityˡ))))
                     (monoₑ ⊩≾̂ₑ-refl (monoₑ (to-witness p) ⊩≾̂ₑ-refl)))
  stepₑ (mergeˡ {a = ac c} {as = as} refl p) q =
    transₑ (monoₑ ⊩≾̂ₑ-refl (monoₑ (to-witness p) ⊩≾̂ₑ-refl))
           (transₑ (eqₑ (≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl ≡̂ₑ-identityˡ)
                                  (≡̂ₑ-sym (consₑ-≡ (ac c) as))))
                   q)
  stepₑ (pick c p) q =
    transₑ (monoₑ (to-witness (lookup-result p)) q) (eqₑ (≡̂ₑ-sym (Commuteₑ.remove-≡ c p)))
  stepₑ (absorbAt c p) q =
    transₑ (monoₑ ⊩≾̂ₑ-refl q)
           (transₑ (eqₑ (≡̂ₑ-trans (≡̂ₑ-cong ≡̂ₑ-refl (Commuteₑ.remove-≡ c p)) (≡̂ₑ-sym ≡̂ₑ-assoc)))
                   (transₑ (monoₑ (transₑ (edgeₑ-sound top) (to-witness (lookup-result p))) ⊩≾̂ₑ-refl)
                           (eqₑ (≡̂ₑ-sym (Commuteₑ.remove-≡ c p)))))
  stepₑ (mergeʳ {a = av _} () _) _
  stepₑ (mergeˡ {a = av _} () _) _

  open Pₑ.Sound (λ as bs → Q ⊩ ⟦ as ⟧ᵉˢ ≾̂ₑ ⟦ bs ⟧ᵉˢ) ⊩≾̂ₑ-refl stepₑ using (prodˢ≾)

  prod≾ₑ : (as bs : List (EAtom Θ))
         → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ bs ⟧ᵉᵖ)
  prod≾ₑ as bs with prodˢ≾ as bs
  ... | just p  = just (transₑ (eqₑ (≡̂ₑ-sym (⟦⟧ᵉᵖ-≡ as)))
                               (transₑ p (eqₑ (⟦⟧ᵉᵖ-≡ bs))))
  ... | nothing = nothing

  -- One alternative against a whole sum: some alternative of the sum
  -- bounds it, and the join is above that one

  altSum≾ₑ : (as : List (EAtom Θ))
           → (t : Alts (List (EAtom Θ)))
           → Maybe (Q ⊩ ⟦ as ⟧ᵉᵖ ≾̂ₑ ⟦ t ⟧ᵉᵖ⁺)
  altSum≾ₑ as (alt P) = prod≾ₑ as P
  altSum≾ₑ as (P ∷⁺ t) with prod≾ₑ as P
  ... | just p  = just (transₑ p ⊔-ubˡₑ)
  ... | nothing with altSum≾ₑ as t
  ...   | just q  = just (transₑ q ⊔-ubʳₑ)
  ...   | nothing = nothing

  -- The whole comparison: every alternative of the left side is below
  -- the right side, and their join is then below it too

  sum≾ₑ : (s t : Alts (List (EAtom Θ)))
        → Maybe (Q ⊩ ⟦ s ⟧ᵉᵖ⁺ ≾̂ₑ ⟦ t ⟧ᵉᵖ⁺)
  sum≾ₑ (alt P)  t = altSum≾ₑ P t
  sum≾ₑ (P ∷⁺ s) t with altSum≾ₑ P t | sum≾ₑ s t
  ... | just p | just q = just (⊔-lubₑ p q)
  ... | _      | _      = nothing

-- The right side is compared folded: each of its groups that varies in
-- one slot is one alternative, above each of the group's members

foldₑ-≡ᵖ : ∀ {Θ} → (ε : EExp Θ) → ε ≡̂ₑ ⟦ foldSumₑ (nrmₑ ε) ⟧ᵉᵖ⁺
foldₑ-≡ᵖ ε =
  ≡̂ₑ-trans (nrmₑ-≡ ε)
  (≡̂ₑ-trans (≡̂ₑ-sym (foldSumₑ-≡ (nrmₑ ε))) (⟦⟧ᵉᵖ⁺-≡ (foldSumₑ (nrmₑ ε))))

deriveₑ : ∀ {Θ} → (Q : Hyps Θ) → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
deriveₑ Q ε ε' with Searchₑ.sum≾ₑ (tableₑ Q) (nrmₑ ε) (foldSumₑ (nrmₑ ε'))
... | just p  = just (transₑ (eqₑ (nrmₑ-≡ᵖ ε)) (transₑ p (eqₑ (≡̂ₑ-sym (foldₑ-≡ᵖ ε')))))
... | nothing = nothing

------------------------------------------------------------------------
-- Resource grades: the same, with a third kind of atom, the image
-- `∣ x ∣` of an effect variable, which is treated as a variable. The
-- unit is below it when either sort's unit is least, the latter
-- carried through the morphism by `map-mono`, as `∣ u ∣ = u`.

∣û∣ₑ : ∀ {Θ} → ûᵣ {Θ} ≡̂ᵣ ∣ ûₑ ∣̂ᵉ
∣û∣ₑ = ≡̂ᵣ-sym (≡̂ᵣ-trans ≡̂ᵣ-map-const
                        (subst (λ c → rconst (mapᵉ uₑ) ≡̂ᵣ rconst c) map-uᵉ ≡̂ᵣ-refl))

module Searchᵣ {Θ} {Q : Hyps Θ}
               (t : Chains.Table (λ a b → Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
                                 ⊩≾̂ᵣ-refl transᵣ linkᵣ? _≟ᵃᵣ_ (edgesᵣ Q)) where

  reachᵣ? : (a b : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  reachᵣ? = Chains.reach? _ ⊩≾̂ᵣ-refl transᵣ linkᵣ? _≟ᵃᵣ_ (edgesᵣ Q) t

  ceilᵣ : ∀ {ρ : RExp Θ} → (b : RAtom Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  ceilᵣ b with reachᵣ? (rc ⊤ᵣ) b
  ... | just p  = just (transᵣ (edgeᵣ-sound top) p)
  ... | nothing = nothing

  atom≾ᵣ : (a b : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  atom≾ᵣ a b = linkᵣ? a b <∣> ceilᵣ b <∣> reachᵣ? a b

  minᵐ : (b : RAtom Θ) → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  minᵐ (rm i) with Is-just? uₑ-least?
  ... | just q  = just (transᵣ (eqᵣ ∣û∣ₑ) (edgeᵣ-sound (img (unit {ε = evar i} q))))
  ... | nothing = nothing
  minᵐ _ = nothing

  unit≾ᵣ : (b : RAtom Θ) → Maybe (Q ⊩ ûᵣ ≾̂ᵣ ⟦ b ⟧ʳᵃ)
  unit≾ᵣ b = min≾ᵣ (Is-just? uᵣ-least?) <∣> minᵐ b <∣> atom≾ᵣ (rc uᵣ) b

  ≾unitᵣ : (a : RAtom Θ) → Maybe (Q ⊩ ⟦ a ⟧ʳᵃ ≾̂ᵣ ûᵣ)
  ≾unitᵣ a = atom≾ᵣ a (rc uᵣ)

  -- The product comparison, its atom comparisons being these

  constʳ? : RAtom Θ → Maybe R
  constʳ? (rc c) = just c
  constʳ? (rv _) = nothing
  constʳ? (rm _) = nothing

  module Pᵣ = Embedding constʳ? (λ c → consᵣ (rc c)) consᵣ-length
                (λ a b → Is-just (atom≾ᵣ a b)) (λ a b → is-just? (atom≾ᵣ a b))
                (λ b → Is-just (unit≾ᵣ b))     (λ b → is-just? (unit≾ᵣ b))
                (λ a → Is-just (≾unitᵣ a))     (λ a → is-just? (≾unitᵣ a))
                (λ b → Is-just (reachᵣ? (rc ⊤ᵣ) b)) (λ b → is-just? (reachᵣ? (rc ⊤ᵣ) b))
                (Is-just ·ᵣ-comm?) (is-just? ·ᵣ-comm?)
  open Pᵣ using (Step; match; skipʳ; skipˡ; absorb; mergeʳ; mergeˡ; pick; absorbAt)

  -- Each step is an entailment, one use of `monoᵣ` on products read
  -- back with a trailing unit (`⟦_⟧ʳˢ`)

  stepᵣ : ∀ {as bs as' bs'} → Step as bs as' bs'
        → Q ⊩ ⟦ as' ⟧ʳˢ ≾̂ᵣ ⟦ bs' ⟧ʳˢ → Q ⊩ ⟦ as ⟧ʳˢ ≾̂ᵣ ⟦ bs ⟧ʳˢ
  stepᵣ (match p)  q = monoᵣ (to-witness p) q
  stepᵣ (skipʳ p)  q = transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-identityˡ)) (monoᵣ (to-witness p) q)
  stepᵣ (skipˡ p)  q = transᵣ (monoᵣ (to-witness p) q) (eqᵣ ≡̂ᵣ-identityˡ)
  stepᵣ (absorb p) q =
    transᵣ (monoᵣ ⊩≾̂ᵣ-refl q)
           (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-assoc)) (monoᵣ (transᵣ (edgeᵣ-sound top) (to-witness p)) ⊩≾̂ᵣ-refl))
  stepᵣ (mergeʳ {a = rc c} {bs = bs} refl p) q =
    transᵣ q (transᵣ (eqᵣ (≡̂ᵣ-trans (consᵣ-≡ (rc c) bs)
                                    (≡̂ᵣ-cong ≡̂ᵣ-refl (≡̂ᵣ-sym ≡̂ᵣ-identityˡ))))
                     (monoᵣ ⊩≾̂ᵣ-refl (monoᵣ (to-witness p) ⊩≾̂ᵣ-refl)))
  stepᵣ (mergeˡ {a = rc c} {as = as} refl p) q =
    transᵣ (monoᵣ ⊩≾̂ᵣ-refl (monoᵣ (to-witness p) ⊩≾̂ᵣ-refl))
           (transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl ≡̂ᵣ-identityˡ)
                                  (≡̂ᵣ-sym (consᵣ-≡ (rc c) as))))
                   q)
  stepᵣ (pick c p) q =
    transᵣ (monoᵣ (to-witness (lookup-result p)) q) (eqᵣ (≡̂ᵣ-sym (Commuteᵣ.remove-≡ c p)))
  stepᵣ (absorbAt c p) q =
    transᵣ (monoᵣ ⊩≾̂ᵣ-refl q)
           (transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-cong ≡̂ᵣ-refl (Commuteᵣ.remove-≡ c p)) (≡̂ᵣ-sym ≡̂ᵣ-assoc)))
                   (transᵣ (monoᵣ (transᵣ (edgeᵣ-sound top) (to-witness (lookup-result p))) ⊩≾̂ᵣ-refl)
                           (eqᵣ (≡̂ᵣ-sym (Commuteᵣ.remove-≡ c p)))))
  stepᵣ (mergeʳ {a = rv _} () _) _
  stepᵣ (mergeʳ {a = rm _} () _) _
  stepᵣ (mergeˡ {a = rv _} () _) _
  stepᵣ (mergeˡ {a = rm _} () _) _

  open Pᵣ.Sound (λ as bs → Q ⊩ ⟦ as ⟧ʳˢ ≾̂ᵣ ⟦ bs ⟧ʳˢ) ⊩≾̂ᵣ-refl stepᵣ using (prodˢ≾)

  prod≾ᵣ : (as bs : List (RAtom Θ))
         → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ bs ⟧ʳᵖ)
  prod≾ᵣ as bs with prodˢ≾ as bs
  ... | just p  = just (transᵣ (eqᵣ (≡̂ᵣ-sym (⟦⟧ʳᵖ-≡ as)))
                               (transᵣ p (eqᵣ (⟦⟧ʳᵖ-≡ bs))))
  ... | nothing = nothing

  altSum≾ᵣ : (as : List (RAtom Θ))
           → (t : Alts (List (RAtom Θ)))
           → Maybe (Q ⊩ ⟦ as ⟧ʳᵖ ≾̂ᵣ ⟦ t ⟧ʳᵖ⁺)
  altSum≾ᵣ as (alt P) = prod≾ᵣ as P
  altSum≾ᵣ as (P ∷⁺ t) with prod≾ᵣ as P
  ... | just p  = just (transᵣ p ⊔-ubˡᵣ)
  ... | nothing with altSum≾ᵣ as t
  ...   | just q  = just (transᵣ q ⊔-ubʳᵣ)
  ...   | nothing = nothing

  sum≾ᵣ : (s t : Alts (List (RAtom Θ)))
        → Maybe (Q ⊩ ⟦ s ⟧ʳᵖ⁺ ≾̂ᵣ ⟦ t ⟧ʳᵖ⁺)
  sum≾ᵣ (alt P)  t = altSum≾ᵣ P t
  sum≾ᵣ (P ∷⁺ s) t with altSum≾ᵣ P t | sum≾ᵣ s t
  ... | just p | just q = just (⊔-lubᵣ p q)
  ... | _      | _      = nothing

foldᵣ-≡ᵖ : ∀ {Θ} → (ρ : RExp Θ) → ρ ≡̂ᵣ ⟦ foldSumᵣ (nrmᵣ ρ) ⟧ʳᵖ⁺
foldᵣ-≡ᵖ ρ =
  ≡̂ᵣ-trans (nrmᵣ-≡ ρ)
  (≡̂ᵣ-trans (≡̂ᵣ-sym (foldSumᵣ-≡ (nrmᵣ ρ))) (⟦⟧ʳᵖ⁺-≡ (foldSumᵣ (nrmᵣ ρ))))

deriveᵣ : ∀ {Θ} → (Q : Hyps Θ) → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
deriveᵣ Q ρ ρ' with Searchᵣ.sum≾ᵣ (tableᵣ Q) (nrmᵣ ρ) (foldSumᵣ (nrmᵣ ρ'))
... | just p  = just (transᵣ (eqᵣ (nrmᵣ-≡ᵖ ρ)) (transᵣ p (eqᵣ (≡̂ᵣ-sym (foldᵣ-≡ᵖ ρ')))))
... | nothing = nothing

------------------------------------------------------------------------
-- The strength `closed`: both sides variable-free, compared by the
-- grade's order along a `cst` edge. An ordering that holds is entailed
-- by every set; one that fails holds at no closed instance.

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

-- The two outcomes of `closed`

data Closedₑ {Θ : Scope} (ε ε' : EExp Θ) : Set where
  holdsₑ : (∀ {Q : Hyps Θ} → Q ⊩ ε ≾̂ₑ ε') → Closedₑ ε ε'
  failsₑ : ((δ : Subst Θ ∅ˢ) → ¬ (∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ)) → Closedₑ ε ε'

data Closedᵣ {Θ : Scope} (ρ ρ' : RExp Θ) : Set where
  holdsᵣ : (∀ {Q : Hyps Θ} → Q ⊩ ρ ≾̂ᵣ ρ') → Closedᵣ ρ ρ'
  failsᵣ : ((δ : Subst Θ ∅ˢ) → ¬ (∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ)) → Closedᵣ ρ ρ'

closedₑ? : ∀ {Θ} → (ε ε' : EExp Θ) → Maybe (Closedₑ ε ε')
closedₑ? ε ε' with valᵉ? ε in q | valᵉ? ε' in q'
... | just c  | just c' with c ≾ₑ? c'
...   | yes p = just (holdsₑ (transₑ (eqₑ (convᵉ ε q))
                                     (transₑ (edgeₑ-sound (cst p)) (eqₑ (≡̂ₑ-sym (convᵉ ε' q'))))))
...   | no n  = just (failsₑ (λ δ d → n (closed-≾ₑ (convᵉ ε q) (convᵉ ε' q') δ d)))
closedₑ? ε ε' | just _  | nothing = nothing
closedₑ? ε ε' | nothing | _       = nothing

closedᵣ? : ∀ {Θ} → (ρ ρ' : RExp Θ) → Maybe (Closedᵣ ρ ρ')
closedᵣ? ρ ρ' with valʳ? ρ in q | valʳ? ρ' in q'
... | just c  | just c' with c ≾ᵣ? c'
...   | yes p = just (holdsᵣ (transᵣ (eqᵣ (convʳ ρ q))
                                     (transᵣ (edgeᵣ-sound (cst p)) (eqᵣ (≡̂ᵣ-sym (convʳ ρ' q'))))))
...   | no n  = just (failsᵣ (λ δ d → n (closed-≾ᵣ (convʳ ρ q) (convʳ ρ' q') δ d)))
closedᵣ? ρ ρ' | just _  | nothing = nothing
closedᵣ? ρ ρ' | nothing | _       = nothing

------------------------------------------------------------------------
-- Decisions at a strength

data Strength : Set where
  closed derive atomic : Strength

-- Membership of an ordering in a list

memʳ? : ∀ {Θ} → (p : RExp Θ × RExp Θ) → (l : List (RExp Θ × RExp Θ)) → Maybe (p ∈ l)
memʳ? p []              = nothing
memʳ? (ρ , ρ') ((ρ₀ , ρ₀') ∷ l) with ρ ≟ʳ ρ₀ | ρ' ≟ʳ ρ₀'
... | yes refl | yes refl = just (here refl)
... | _        | _        with memʳ? (ρ , ρ') l
...   | just m  = just (there m)
...   | nothing = nothing

memᵉ? : ∀ {Θ} → (p : EExp Θ × EExp Θ) → (l : List (EExp Θ × EExp Θ)) → Maybe (p ∈ l)
memᵉ? p []              = nothing
memᵉ? (ε , ε') ((ε₀ , ε₀') ∷ l) with ε ≟ᵉ ε₀ | ε' ≟ᵉ ε₀'
... | yes refl | yes refl = just (here refl)
... | _        | _        with memᵉ? (ε , ε') l
...   | just m  = just (there m)
...   | nothing = nothing

decideₑ : ∀ {Θ} → Strength → (Q : Hyps Θ) → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
decideₑ closed Q ε ε' with closedₑ? ε ε'
... | just (holdsₑ p) = just p
... | _               = nothing
decideₑ derive Q ε ε' = deriveₑ Q ε ε'
decideₑ atomic Q ε ε' with memᵉ? (ε , ε') (ordₑ Q)
... | just m  = just (edgeₑ-sound (hyp m))
... | nothing = deriveₑ Q ε ε'

decideᵣ : ∀ {Θ} → Strength → (Q : Hyps Θ) → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
decideᵣ closed Q ρ ρ' with closedᵣ? ρ ρ'
... | just (holdsᵣ p) = just p
... | _               = nothing
decideᵣ derive Q ρ ρ' = deriveᵣ Q ρ ρ'
decideᵣ atomic Q ρ ρ' with memʳ? (ρ , ρ') (ordᵣ Q)
... | just m  = just (edgeᵣ-sound (hyp m))
... | nothing = deriveᵣ Q ρ ρ'

------------------------------------------------------------------------
-- Refutation of `ρ ≾ u` by the zero-product law
--
-- A constant atom of `ρ`'s normal form that is not itself below the
-- unit refutes every alternative it occurs in, by the zero-product
-- laws of `_≾ᵣ_`; every alternative is below the sum, so one refuted
-- alternative refutes the whole. Refutation is stable under
-- instantiation and rules out entailment from every satisfiable set;
-- it cannot be quantified over all `Q` (`hyp-derives`).

-- No closed instance brings the expression below the unit

Refutedᵤ : ∀ {Ψ} → RExp Ψ → Set
Refutedᵤ {Ψ} ρ = (δ : Subst Ψ ∅ˢ) → ¬ (valʳ (ρ [ δ ]ʳ) ≾ᵣ uᵣ)

-- A product below the unit has both halves below the unit, so a
-- refutation of either half refutes the product

head-refutes : ∀ {Ψ} → (a : RAtom Ψ) → (as : List (RAtom Ψ))
             → Refutedᵤ ⟦ a ⟧ʳᵃ → Refutedᵤ ⟦ a ∷ as ⟧ʳˢ
head-refutes a as ref δ le = ref δ (≾ᵣ-zero-productˡ le)

tail-refutes : ∀ {Ψ} → (a : RAtom Ψ) → (as : List (RAtom Ψ))
             → Refutedᵤ ⟦ as ⟧ʳˢ → Refutedᵤ ⟦ a ∷ as ⟧ʳˢ
tail-refutes a as ref δ le = ref δ (≾ᵣ-zero-productʳ le)

-- A constant that is not below the unit, and a join one of whose
-- operands is refuted

const-refutes : ∀ {Ψ} {c : R} → ¬ (c ≾ᵣ uᵣ) → Refutedᵤ (rconst {Ψ} c)
const-refutes ¬p δ le = ¬p le

join-refutesˡ : ∀ {Ψ} {ρ ρ' : RExp Ψ} → Refutedᵤ ρ → Refutedᵤ (ρ ⊔̂ᵣ ρ')
join-refutesˡ {ρ = ρ} {ρ' = ρ'} ref δ le =
  ref δ (≾ᵣ-trans (⊔ᵣ-ubˡ (valʳ (ρ [ δ ]ʳ)) (valʳ (ρ' [ δ ]ʳ))) le)

join-refutesʳ : ∀ {Ψ} {ρ ρ' : RExp Ψ} → Refutedᵤ ρ' → Refutedᵤ (ρ ⊔̂ᵣ ρ')
join-refutesʳ {ρ = ρ} {ρ' = ρ'} ref δ le =
  ref δ (≾ᵣ-trans (⊔ᵣ-ubʳ (valʳ (ρ [ δ ]ʳ)) (valʳ (ρ' [ δ ]ʳ))) le)

-- Transported along a convertibility, and so along the certified
-- normalisation

refute-≡̂ᵣ : ∀ {Ψ} {ρ ρ' : RExp Ψ} → ρ ≡̂ᵣ ρ' → Refutedᵤ ρ' → Refutedᵤ ρ
refute-≡̂ᵣ eq ref δ le = ref δ (subst (_≾ᵣ uᵣ) (inst-≡̂ᵣ δ eq) le)

-- Refutation survives every later instantiation

refute-[]ʳ : ∀ {Ψ Ψ'} {ρ : RExp Ψ} → (σ : Subst Ψ Ψ')
           → Refutedᵤ ρ → Refutedᵤ (ρ [ σ ]ʳ)
refute-[]ʳ {ρ = ρ} σ ref δ le = ref (σ ⨟ˢ δ) (subst (λ x → valʳ x ≾ᵣ uᵣ) ([⨟]ʳ ρ σ δ) le)

-- A refuted expression is entailed by no satisfiable hypothesis set

refute-⊩ : ∀ {Ψ} {ρ : RExp Ψ} {Q : Hyps Ψ} → Satisfiable Q []
         → Refutedᵤ ρ → ¬ (Q ⊩ ρ ≾̂ᵣ ûᵣ)
refute-⊩ (δ , h ∷ []) ref d = ref δ (inst-≾ᵣ h d)

-- Satisfiability is essential: a hypothesis names any ordering at all

hyp-derives : ∀ {Ψ} → (ρ : RExp Ψ) → hyps [] [] ((ρ , ûᵣ) ∷ []) [] [] ⊩ ρ ≾̂ᵣ ûᵣ
hyp-derives ρ = hypᵣ (here refl)

-- The scan is structural over the alternatives of the sum and over
-- the atoms of each

scan-atom : ∀ {Ψ} → (a : RAtom Ψ) → Maybe (Refutedᵤ ⟦ a ⟧ʳᵃ)
scan-atom (rv i) = nothing
scan-atom (rm i) = nothing
scan-atom (rc c) with c ≾ᵣ? uᵣ
... | yes _ = nothing
... | no ¬p = just (const-refutes ¬p)

scan-atoms : ∀ {Ψ} → (as : List (RAtom Ψ)) → Maybe (Refutedᵤ ⟦ as ⟧ʳˢ)
scan-atoms []       = nothing
scan-atoms (a ∷ as) with scan-atom a | scan-atoms as
... | just r  | _      = just (head-refutes a as r)
... | nothing | just r = just (tail-refutes a as r)
... | nothing | nothing = nothing

scan-sum : ∀ {Ψ} → (s : Alts (List (RAtom Ψ))) → Maybe (Refutedᵤ ⟦ s ⟧ʳˢ⁺)
scan-sum (alt P)  = scan-atoms P
scan-sum (P ∷⁺ t) with scan-atoms P | scan-sum t
... | just r  | _      = just (join-refutesˡ {ρ = ⟦ P ⟧ʳˢ} {ρ' = ⟦ t ⟧ʳˢ⁺} r)
... | nothing | just r = just (join-refutesʳ {ρ = ⟦ P ⟧ʳˢ} {ρ' = ⟦ t ⟧ʳˢ⁺} r)
... | nothing | nothing = nothing

refute≾u : ∀ {Ψ} → (ρ : RExp Ψ) → Maybe (Refutedᵤ ρ)
refute≾u ρ with scan-sum (nrmᵣ ρ)
... | nothing = nothing
... | just r  = just (refute-≡̂ᵣ (nrmᵣ-≡ ρ) r)

------------------------------------------------------------------------
-- The closed check
--
-- `checkClosed` decides at the strength `closed` every ordering of a
-- set and every ordering between two closed sides joined by a chain
-- of `hyp` edges (`Transitive`, over `Reach`): it drops each one that
-- holds and fails on one that does not. A var-rule disjunction whose
-- grade has a value is decided against the unit in the same way: it
-- is dropped when the ordering holds, and the check fails when the
-- ordering does not hold and the type is refuted eternal (`etDec`).
-- Other atoms are kept unchanged.

-- A closed ordering that fails

Falseʳ : ∀ {Θ} → List (RExp Θ × RExp Θ) → Set
Falseʳ {Θ} l = Σ[ ρ ∈ RExp Θ ] Σ[ ρ' ∈ RExp Θ ]
                 ((ρ , ρ') ∈ l × ((δ : Subst Θ ∅ˢ) → ¬ (∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ)))

Falseᵉ : ∀ {Θ} → List (EExp Θ × EExp Θ) → Set
Falseᵉ {Θ} l = Σ[ ε ∈ EExp Θ ] Σ[ ε' ∈ EExp Θ ]
                 ((ε , ε') ∈ l × ((δ : Subst Θ ∅ˢ) → ¬ (∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ)))

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

dropʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} {ρ ρ'}
      → (∀ {Q : Hyps Θ} → Q ⊩ ρ ≾̂ᵣ ρ') → Keptʳ l → Keptʳ ((ρ , ρ') ∷ l)
dropʳ p k =
  keptʳ (lʳ k) (λ m → there (subʳ k m))
        (λ δ f → λ { (here refl) → ⊩-substᵣ (⊩ᴴ-∅ {σ = δ}) p
                   ; (there m)   → entʳ k δ f m })

dropᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} {ε ε'}
      → (∀ {Q : Hyps Θ} → Q ⊩ ε ≾̂ₑ ε') → Keptᵉ l → Keptᵉ ((ε , ε') ∷ l)
dropᵉ p k =
  keptᵉ (lᵉ k) (λ m → there (subᵉ k m))
        (λ δ f → λ { (here refl) → ⊩-substₑ (⊩ᴴ-∅ {σ = δ}) p
                   ; (there m)   → entᵉ k δ f m })

thereʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} {p} → Falseʳ l → Falseʳ (p ∷ l)
thereʳ (ρ , ρ' , m , n) = ρ , ρ' , there m , n

thereᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} {p} → Falseᵉ l → Falseᵉ (p ∷ l)
thereᵉ (ε , ε' , m , n) = ε , ε' , there m , n

closedʳ : ∀ {Θ} → (l : List (RExp Θ × RExp Θ)) → Falseʳ l ⊎ Keptʳ l
closedʳ [] = inj₂ (keptʳ [] (λ ()) (λ δ k → λ ()))
closedʳ ((ρ , ρ') ∷ l) with closedʳ l
... | inj₁ f = inj₁ (thereʳ f)
... | inj₂ k with closedᵣ? ρ ρ'
...   | just (holdsᵣ p) = inj₂ (dropʳ p k)
...   | just (failsᵣ n) = inj₁ (ρ , ρ' , here refl , n)
...   | nothing         = inj₂ (consʳ k)

closedᵉ : ∀ {Θ} → (l : List (EExp Θ × EExp Θ)) → Falseᵉ l ⊎ Keptᵉ l
closedᵉ [] = inj₂ (keptᵉ [] (λ ()) (λ δ k → λ ()))
closedᵉ ((ε , ε') ∷ l) with closedᵉ l
... | inj₁ f = inj₁ (thereᵉ f)
... | inj₂ k with closedₑ? ε ε'
...   | just (holdsₑ p) = inj₂ (dropᵉ p k)
...   | just (failsₑ n) = inj₁ (ε , ε' , here refl , n)
...   | nothing         = inj₂ (consᵉ k)

-- A failing closed ordering holds at no closed instance

falseʳ : ∀ {Θ} {l : List (RExp Θ × RExp Θ)} → Falseʳ l → (δ : Subst Θ ∅ˢ)
       → (∀ {ρ ρ'} → (ρ , ρ') ∈ l → ∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ρ' [ δ ]ʳ) → ⊥
falseʳ (ρ , ρ' , m , n) δ k = n δ (k m)

falseᵉ : ∀ {Θ} {l : List (EExp Θ × EExp Θ)} → Falseᵉ l → (δ : Subst Θ ∅ˢ)
       → (∀ {ε ε'} → (ε , ε') ∈ l → ∅ᴴ ⊩ ε [ δ ]ᵉ ≾̂ₑ ε' [ δ ]ᵉ) → ⊥
falseᵉ (ε , ε' , m , n) δ k = n δ (k m)

-- Var-rule disjunctions: one whose grade has a value above the unit,
-- at a type refuted eternal, fails

Falseᵈ : ∀ {Θ} → List (OVType Θ × RExp Θ) → Set
Falseᵈ {Θ} l = Σ[ A ∈ OVType Θ ] Σ[ ρ ∈ RExp Θ ]
                 ((A , ρ) ∈ l × etDec A ≡ nothing
                  × ((δ : Subst Θ ∅ˢ) → ¬ (∅ᴴ ⊩ ρ [ δ ]ʳ ≾̂ᵣ ûᵣ)))

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

dropᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} {A ρ}
      → (∀ {Q : Hyps Θ} → Q ⊩ ρ ≾̂ᵣ ûᵣ) → Keptᵈ l → Keptᵈ ((A , ρ) ∷ l)
dropᵈ p k =
  keptᵈ (lᵈ k) (λ m → there (subᵈ k m))
        (λ δ f → λ { (here refl) → ≾ᵘ-ok (⊩-substᵣ (⊩ᴴ-∅ {σ = δ}) p)
                   ; (there m)   → entᵈ k δ f m })

thereᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} {p} → Falseᵈ l → Falseᵈ (p ∷ l)
thereᵈ (A , ρ , m , e , n) = A , ρ , there m , e , n

closedᵈ : ∀ {Θ} → (l : List (OVType Θ × RExp Θ)) → Falseᵈ l ⊎ Keptᵈ l
closedᵈ [] = inj₂ (keptᵈ [] (λ ()) (λ δ k → λ ()))
closedᵈ ((A , ρ) ∷ l) with closedᵈ l
... | inj₁ f = inj₁ (thereᵈ f)
... | inj₂ k with closedᵣ? ρ ûᵣ
...   | nothing         = inj₂ (consᵈ k)
...   | just (holdsᵣ p) = inj₂ (dropᵈ p k)
...   | just (failsᵣ n) with etDec A in e
...     | nothing = inj₁ (A , ρ , here refl , e , n)
...     | just _  = inj₂ (consᵈ k)

falseᵈ : ∀ {Θ} {l : List (OVType Θ × RExp Θ)} → Falseᵈ l → (δ : Subst Θ ∅ˢ)
       → (∀ {A ρ} → (A , ρ) ∈ l → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ)) → ⊥
falseᵈ (A , ρ , m , e , n) δ k with VarOK-∅ (k m)
... | inj₁ et = etDec-refute A e δ et
... | inj₂ le = n δ (val-≾ᵣ⁻ le)

------------------------------------------------------------------------
-- The orderings a list entails by transitivity
--
-- The sides of the orderings are the vertices and the orderings the
-- edges, the `hyp` edges of the hypothesis graph, closed by `Reach`.
-- A pair of closed sides joined by a chain of two or more edges is
-- entailed; a shorter chain is an ordering of the list or reflexive.

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

checkClosed : ∀ {Θ} → Hyps Θ → Maybe (Hyps Θ)
checkClosed Q with closedʳ (withChainsʳ (ordᵣ Q)) | closedᵉ (withChainsᵉ (ordₑ Q)) | closedᵈ (disj Q)
... | inj₂ kʳ | inj₂ kᵉ | inj₂ kᵈ =
      just (hyps (ets Q) (subᵥ Q) (lʳ kʳ) (lᵉ kᵉ) (lᵈ kᵈ))
... | _       | _       | _       = nothing

-- What is left entails the set

checkClosed-⊩ : ∀ {Θ} → (Q : Hyps Θ) → {Q₁ : Hyps Θ} → checkClosed Q ≡ just Q₁ → Q₁ ⊩ᴴ Q [ idˢ ]
checkClosed-⊩ Q eq with closedʳ (withChainsʳ (ordᵣ Q)) | closedᵉ (withChainsᵉ (ordₑ Q)) | closedᵈ (disj Q)
checkClosed-⊩ Q refl | inj₂ kʳ | inj₂ kᵉ | inj₂ kᵈ =
  mk⊩ᴴ (⊩ets r) (⊩subᵥ r) (λ m → entʳ kʳ idˢ (⊩ordᵣ r) (∈-++⁺ˡ m))
       (λ m → entᵉ kᵉ idˢ (⊩ordₑ r) (∈-++⁺ˡ m)) (entᵈ kᵈ idˢ (⊩disj r))
  where r = ⊩ᴴ-refl {Q = hyps (ets Q) (subᵥ Q) (lʳ kʳ) (lᵉ kᵉ) (lᵈ kᵈ)}
checkClosed-⊩ Q () | inj₁ _ | _      | _
checkClosed-⊩ Q () | inj₂ _ | inj₁ _ | _
checkClosed-⊩ Q () | inj₂ _ | inj₂ _ | inj₁ _

-- and is entailed wherever the set is, its chains being composed of
-- `hyp` edges

checkClosed-⊆ : ∀ {Θ Θ'} → (Q : Hyps Θ) → {Q₁ : Hyps Θ} → checkClosed Q ≡ just Q₁
              → {Q' : Hyps Θ'} {δ : Subst Θ Θ'} → Q' ⊩ᴴ Q [ δ ] → Q' ⊩ᴴ Q₁ [ δ ]
checkClosed-⊆ Q eq h with closedʳ (withChainsʳ (ordᵣ Q)) | closedᵉ (withChainsᵉ (ordₑ Q)) | closedᵈ (disj Q)
checkClosed-⊆ Q refl h | inj₂ kʳ | inj₂ kᵉ | inj₂ kᵈ =
  mk⊩ᴴ (⊩ets h) (⊩subᵥ h)
       (λ m → withChainsʳ-⊩ (ordᵣ Q) (λ m' → ⊩-substᵣ h (edgeᵣ-sound (hyp m'))) (subʳ kʳ m))
       (λ m → withChainsᵉ-⊩ (ordₑ Q) (λ m' → ⊩-substₑ h (edgeₑ-sound (hyp m'))) (subᵉ kᵉ m))
       (λ m → ⊩disj h (subᵈ kᵈ m))
checkClosed-⊆ Q () h | inj₁ _ | _      | _
checkClosed-⊆ Q () h | inj₂ _ | inj₁ _ | _
checkClosed-⊆ Q () h | inj₂ _ | inj₂ _ | inj₁ _

-- A failure leaves the set unsatisfiable

checkClosed-fail : ∀ {Θ} → (Q : Hyps Θ) → checkClosed Q ≡ nothing → ¬ Satisfiable Q []
checkClosed-fail Q eq (δ , h ∷ []) with closedʳ (withChainsʳ (ordᵣ Q)) | closedᵉ (withChainsᵉ (ordₑ Q)) | closedᵈ (disj Q)
... | inj₁ f | _      | _      =
      falseʳ f δ (withChainsʳ-⊩ (ordᵣ Q) (λ m → ⊩-substᵣ h (edgeᵣ-sound (hyp m))))
... | inj₂ _ | inj₁ f | _      =
      falseᵉ f δ (withChainsᵉ-⊩ (ordₑ Q) (λ m → ⊩-substₑ h (edgeₑ-sound (hyp m))))
... | inj₂ _ | inj₂ _ | inj₁ f = falseᵈ f δ (⊩disj h)
checkClosed-fail Q () (δ , h ∷ []) | inj₂ _ | inj₂ _ | inj₂ _
