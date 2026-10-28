------------------------------------------------------------------
-- The instantiation theorem                                    --
--                                                              --
-- An open typing under `Q` is a family of declarative typings, --
-- one per instance satisfying `Q`: for every declarative       --
-- instance `σ` of the type, resource-grade and effect-grade    --
-- variables with `σ ⊨ᴰ Q`, a derivation `Q ∣ Γ ⊢C⦂ C` of a     --
-- term whose handlers are second-class (`SecondClassᶜ`) gives  --
-- a derivation `⟦ Γ ⟧ᶜᵗˣ σ ⊢C⦂ ⟦ C ⟧ᶜ σ` of the term's         --
-- elaboration in the declarative calculus (`instantiateᶜ`; a   --
-- value `V` as `return V`, `instantiateᵛ`).                    --
--                                                              --
-- The typing is built rule by rule, each side condition by the --
-- soundness of entailment and the annotation rules as their    --
-- subjects. `handle M with handler H` is the closed `handle`,  --
-- the handler's subsumptions moved to `M` and to the result    --
-- (`instʰ`). A handler clause, typed at a rigid continuation   --
-- grade, is instantiated at every extension `σ ,ᵉᴰ c`, which   --
-- gives the closed clause family. A comparison, a value here   --
-- and a computation there, is hoisted: the comparisons of a    --
-- computation's values, outside their functions, are run just  --
-- before it, inner ones first and left to right, each binding  --
-- its outcome, which the value then reads. The operands are of --
-- eternal type, so a comparison in a boxed value is run before --
-- the box, outside its lock.                                   --
--                                                              --
-- In the open syntax: for every closed instance `δ` with       --
-- `δ ⊨ Q ∣ []`, the elaboration of `M [ δ ]ᴿᶜ` is typed at     --
-- `⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⊢C⦂ ⌞ C [ δ ]ᶜ ⌟ᶜ` (`instantiateˢᶜ`,      --
-- `instantiateˢᵛ`), the declarative theorem at `⌞ δ ⌟ˢ`        --
-- through the correspondence of the two kinds of instance.     --
--                                                              --
-- The elaboration is a function of the raw term (`⌊_⌋ᴿᶜ`):     --
-- the closed erasure of the typing is the elaboration of the   --
-- open erasure at `σ`, type annotations forgotten, box grades  --
-- evaluated and comparisons hoisted. A raw term substituted by --
-- `δ` elaborates at `σ` as the term at `δ ⨟ᴰ σ` (`⌊[]⌋ᴿᶜ`).    --
------------------------------------------------------------------

open import Data.Fin using (toℕ)
open import Data.List.Base using ([])
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)

open import Grades.Base
open import Language.Spec
open import Language.Operations
open import Language.Comparisons using (Cmp)

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module Bridge.Instantiation.Terms (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Language.Types                 S
open import ClosedCalculus.Syntax.Contexts S
open import ClosedCalculus.Syntax.Terms    S
open import ClosedCalculus.Syntax.Erasure  S hiding (⌊_⌋ᵛ; ⌊_⌋ᶜ; var-pos)
import ClosedCalculus.Syntax.Erasure S as CE

open import OpenCalculus.Syntax.Grades    S
open import OpenCalculus.Syntax.Types     S
open import OpenCalculus.Syntax.Contexts  S
open import OpenCalculus.Syntax.Subst     S
open import OpenCalculus.Hypotheses       S
open import OpenCalculus.Typing           S
open import OpenCalculus.Syntax.Raw       S
open import OpenCalculus.Syntax.Raw.Subst S
import OpenCalculus.Typing.Erasure S as OE
open import OpenCalculus.Hypotheses.Instances S using (_⊨_∣_)

open import Bridge.Instantiation.Types          S
open import Bridge.Instantiation.Judgements     S
open import Bridge.Instantiation.Correspondence S
open import Bridge.Instantiation.Hoisting       S

------------------------------------------------------------------------
-- The elaboration of raw terms at a declarative instance, the raw map
-- giving the positions of the term's variables

-- The comparisons of two values hoisted in turn, the second's after the
-- first's

pairᵗ : RTel × Envᴿ → (RTel → RTel × Envᴿ) → RTel × Envᴿ
pairᵗ (T , E) k = T ++ᴿ proj₁ (k T) , wkᴿ (proj₁ (k T)) E ⊗ᴿ proj₂ (k T)

pairʰ : (RMap → RTel × Envᴿ) → (RMap → RTel × Envᴿ) → RMap → RTel × Envᴿ
pairʰ f g r = pairᵗ (f r) (λ T → g (r ⊕ᴿ T))

-- A comparison hoisted after those of its operands, the operands built
-- at its point

cmpᵗ : Cmp → (RMap → Envᴿ → ErV) → (RMap → Envᴿ → ErV) → RMap
     → RTel × Envᴿ → RTel × Envᴿ
cmpᵗ ⋈ a b r (T , E) = T ▷ cmpᴿ ⋈ (a (r ⊕ᴿ T) (leftᴱ E)) (b (r ⊕ᴿ T) (rightᴱ E)) , outᴿ 0

cmpʰ : Cmp → (RMap → RTel × Envᴿ) → (RMap → RTel × Envᴿ)
     → (RMap → Envᴿ → ErV) → (RMap → Envᴿ → ErV) → RMap → RTel × Envᴿ
cmpʰ ⋈ f g a b r = cmpᵗ ⋈ a b r (pairʰ f g r)

-- A computation run after the comparisons hoisted from its values

on₁ᵗ : (RMap → Envᴿ → ErC) → RMap → RTel × Envᴿ → ErC
on₁ᵗ K r (T , E) = wrapᴿ T (K (r ⊕ᴿ T) E)

on₁ᴿ : (RMap → RTel × Envᴿ) → (RMap → Envᴿ → ErC) → RMap → ErC
on₁ᴿ f K r = on₁ᵗ K r (f r)

-- The outcome variable of a comparison

outᴱ : Envᴿ → ℕ
outᴱ (outᴿ k) = k
outᴱ _        = 0

mutual

  hoistᴿ : ∀ {Θ n} → RawV Θ n → DInst Θ → RMap → RTel × Envᴿ
  hoistᴿ (succ V)    σ = hoistᴿ V σ
  hoistᴿ ⦉ V , W ⦊    σ = pairʰ (hoistᴿ V σ) (hoistᴿ W σ)
  hoistᴿ (inl V)     σ = hoistᴿ V σ
  hoistᴿ (inr V)     σ = hoistᴿ V σ
  hoistᴿ (cons V W)  σ = pairʰ (hoistᴿ V σ) (hoistᴿ W σ)
  hoistᴿ (cmp ⋈ V W) σ = cmpʰ ⋈ (hoistᴿ V σ) (hoistᴿ W σ) (buildᴿ V σ) (buildᴿ W σ)
  hoistᴿ (V ⦂ᵛ A)    σ = hoistᴿ V σ
  hoistᴿ (var i)     σ = λ r → [] , ∅ᴿ
  hoistᴿ (const B c) σ = λ r → [] , ∅ᴿ
  hoistᴿ ⋆           σ = λ r → [] , ∅ᴿ
  hoistᴿ true        σ = λ r → [] , ∅ᴿ
  hoistᴿ false       σ = λ r → [] , ∅ᴿ
  hoistᴿ zero        σ = λ r → [] , ∅ᴿ
  hoistᴿ nil         σ = λ r → [] , ∅ᴿ
  hoistᴿ (lam M)     σ = λ r → [] , ∅ᴿ
  hoistᴿ (handler N H) σ = λ r → [] , ∅ᴿ

  -- a value, its comparisons read off their outcome variables

  buildᴿ : ∀ {Θ n} → RawV Θ n → DInst Θ → RMap → Envᴿ → ErV
  buildᴿ (var i)     σ r e = var (posᴿ r (toℕ i))
  buildᴿ (const B c) σ r e = const B c
  buildᴿ ⋆           σ r e = ⋆
  buildᴿ true        σ r e = true
  buildᴿ false       σ r e = false
  buildᴿ zero        σ r e = zero
  buildᴿ (succ V)    σ r e = succ (buildᴿ V σ r e)
  buildᴿ ⦉ V , W ⦊    σ r e = ⦉ buildᴿ V σ r (leftᴱ e) , buildᴿ W σ r (rightᴱ e) ⦊
  buildᴿ (inl V)     σ r e = inl (buildᴿ V σ r e)
  buildᴿ (inr V)     σ r e = inr (buildᴿ V σ r e)
  buildᴿ nil         σ r e = nil
  buildᴿ (cons V W)  σ r e = cons (buildᴿ V σ r (leftᴱ e)) (buildᴿ W σ r (rightᴱ e))
  buildᴿ (cmp ⋈ V W) σ r e = var (outᴱ e)
  buildᴿ (lam M)     σ r e = lam (elabᶜ M σ (extᴿ r))
  buildᴿ (handler N H) σ r e = ⋆
  buildᴿ (V ⦂ᵛ A)    σ r e = buildᴿ V σ r e

  -- a handler has no closed counterpart of its own: `handle M with V`
  -- elaborates to the closed `handle` when `V` is a handler, its clauses,
  -- over one more effect-grade variable, taken at each continuation
  -- grade; a handler elsewhere, and a `handle` whose handler is not one,
  -- elaborate to `⋆` and to the handled computation

  elabᶜ : ∀ {Θ n} → RawC Θ n → DInst Θ → RMap → ErC
  elabᶜ (return V) σ =
    on₁ᴿ (hoistᴿ V σ) (λ r e → return (buildᴿ V σ r e))
  elabᶜ (M ⨟ N) σ r = elabᶜ M σ r ⨟ elabᶜ N σ (extᴿ r)
  elabᶜ (V · W) σ =
    on₁ᴿ (pairʰ (hoistᴿ V σ) (hoistᴿ W σ))
         (λ r e → buildᴿ V σ r (leftᴱ e) · buildᴿ W σ r (rightᴱ e))
  elabᶜ (match V `in M) σ =
    on₁ᴿ (hoistᴿ V σ) (λ r e → match buildᴿ V σ r e `in elabᶜ M σ (extᴿ (extᴿ r)))
  elabᶜ (absurd V) σ =
    on₁ᴿ (hoistᴿ V σ) (λ r e → absurd (buildᴿ V σ r e))
  elabᶜ (if V `then M `else N) σ =
    on₁ᴿ (hoistᴿ V σ) (λ r e → if buildᴿ V σ r e `then elabᶜ M σ r `else elabᶜ N σ r)
  elabᶜ (caseℕ V `zero M `succ N) σ =
    on₁ᴿ (hoistᴿ V σ)
         (λ r e → caseℕ buildᴿ V σ r e `zero elabᶜ M σ r `succ elabᶜ N σ (extᴿ r))
  elabᶜ (case+ V `inl M `inr N) σ =
    on₁ᴿ (hoistᴿ V σ)
         (λ r e → case+ buildᴿ V σ r e `inl elabᶜ M σ (extᴿ r) `inr elabᶜ N σ (extᴿ r))
  elabᶜ (recℕ V M N) σ =
    on₁ᴿ (hoistᴿ V σ)
         (λ r e → recℕ (buildᴿ V σ r e) (elabᶜ M σ r) (elabᶜ N σ (extᴿ (extᴿ r))))
  elabᶜ (caseL V `nil M `cons N) σ =
    on₁ᴿ (hoistᴿ V σ)
         (λ r e → caseL buildᴿ V σ r e `nil elabᶜ M σ r `cons elabᶜ N σ (extᴿ (extᴿ r)))
  elabᶜ (recL V M N) σ =
    on₁ᴿ (hoistᴿ V σ)
         (λ r e → recL (buildᴿ V σ r e) (elabᶜ M σ r) (elabᶜ N σ (extᴿ (extᴿ (extᴿ r)))))
  elabᶜ (perform op V M) σ =
    on₁ᴿ (hoistᴿ V σ) (λ r e → perform op (buildᴿ V σ r e) (elabᶜ M σ (extᴿ r)))
  elabᶜ (delay τ M) σ r = delay τ (elabᶜ M σ r)
  elabᶜ (handle M `with V) σ r = elabʰ M V σ r
  elabᶜ (unbox i N) σ r = unbox (posᴿ r (toℕ i)) (elabᶜ N σ (extᴿ r))
  elabᶜ (box ρ V N) σ =
    on₁ᴿ (hoistᴿ V σ) (λ r e → box (⟦ ρ ⟧ʳ σ) (buildᴿ V σ r e) (elabᶜ N σ (extᴿ r)))
  elabᶜ (M ⦂ᶜ C) σ r = elabᶜ M σ r

  elabʰ : ∀ {Θ n} → RawC Θ n → RawV Θ n → DInst Θ → RMap → ErC
  elabʰ M (handler N H) σ r =
    handle elabᶜ M σ r
      `with (λ op c → elabᶜ (H op) (σ ,ᵉᴰ c) (extᴿ (extᴿ r)))
      `in (elabᶜ N σ (extᴿ r))
  elabʰ M (var i) σ r = elabᶜ M σ r
  elabʰ M (const B c) σ r = elabᶜ M σ r
  elabʰ M ⋆ σ r = elabᶜ M σ r
  elabʰ M true σ r = elabᶜ M σ r
  elabʰ M false σ r = elabᶜ M σ r
  elabʰ M zero σ r = elabᶜ M σ r
  elabʰ M (succ U) σ r = elabᶜ M σ r
  elabʰ M ⦉ U , U' ⦊ σ r = elabᶜ M σ r
  elabʰ M (inl U) σ r = elabᶜ M σ r
  elabʰ M (inr U) σ r = elabᶜ M σ r
  elabʰ M nil σ r = elabᶜ M σ r
  elabʰ M (cons U U') σ r = elabᶜ M σ r
  elabʰ M (cmp ⋈ U U') σ r = elabᶜ M σ r
  elabʰ M (lam L) σ r = elabᶜ M σ r
  elabʰ M (U ⦂ᵛ A) σ r = elabᶜ M σ r

-- The elaboration of a term

⌊_⌋ᴿᶜ : ∀ {Θ n} → RawC Θ n → DInst Θ → ErC
⌊ M ⌋ᴿᶜ σ = elabᶜ M σ idᴿ

-- A closed raw term means its elaboration at the empty instance

⌞_⌟ᴿᶜ : ∀ {n} → RawC ∅ˢ n → ErC
⌞ M ⌟ᴿᶜ = ⌊ M ⌋ᴿᶜ ∅ᴰ

------------------------------------------------------------------------
-- The combinators respect pointwise equality of their arguments

pairᵗ-at : (p : RTel × Envᴿ) → (k k' : RTel → RTel × Envᴿ)
         → k (proj₁ p) ≡ k' (proj₁ p) → pairᵗ p k ≡ pairᵗ p k'
pairᵗ-at (T , E) k k' e = cong (λ x → T ++ᴿ proj₁ x , wkᴿ (proj₁ x) E ⊗ᴿ proj₂ x) e

pairʰ-cong : ∀ {f f' g g' : RMap → RTel × Envᴿ}
           → (∀ r → f r ≡ f' r) → (∀ r → g r ≡ g' r) → ∀ r → pairʰ f g r ≡ pairʰ f' g' r
pairʰ-cong {f} {f'} {g} {g'} p q r =
  trans (cong (λ x → pairᵗ x (λ T → g (r ⊕ᴿ T))) (p r))
        (pairᵗ-at (f' r) (λ T → g (r ⊕ᴿ T)) (λ T → g' (r ⊕ᴿ T)) (q (r ⊕ᴿ proj₁ (f' r))))

cmpʰ-cong : ∀ {⋈} {f f' g g' : RMap → RTel × Envᴿ} {a a' b b' : RMap → Envᴿ → ErV}
          → (∀ r → f r ≡ f' r) → (∀ r → g r ≡ g' r)
          → (∀ r e → a r e ≡ a' r e) → (∀ r e → b r e ≡ b' r e)
          → ∀ r → cmpʰ ⋈ f g a b r ≡ cmpʰ ⋈ f' g' a' b' r
cmpʰ-cong {⋈} {f' = f'} {g' = g'} {a} {a'} {b} {b'} p q u v r =
  trans (cong (cmpᵗ ⋈ a b r) (pairʰ-cong p q r)) (at (pairʰ f' g' r))
  where
    at : ∀ x → cmpᵗ ⋈ a b r x ≡ cmpᵗ ⋈ a' b' r x
    at (T , E) = cong₂ (λ y z → T ▷ cmpᴿ ⋈ y z , outᴿ 0) (u _ _) (v _ _)

on₁ᴿ-cong : ∀ {f f' : RMap → RTel × Envᴿ} {K K' : RMap → Envᴿ → ErC}
          → (∀ r → f r ≡ f' r) → (∀ r e → K r e ≡ K' r e) → ∀ r → on₁ᴿ f K r ≡ on₁ᴿ f' K' r
on₁ᴿ-cong {f' = f'} {K = K} {K'} p q r = trans (cong (on₁ᵗ K r) (p r)) (at (f' r))
  where
    at : ∀ x → on₁ᵗ K r x ≡ on₁ᵗ K' r x
    at (T , E) = cong (wrapᴿ T) (q _ _)

-- Pointwise equal instances give the same elaboration. The handler case
-- compares clause families, functions, and so uses `fun-ext`.

mutual

  ⌊≗⌋ʰ : ∀ {Θ n} {σ σ' : DInst Θ} → σ ≗ᴰ σ' → (V : RawV Θ n)
       → ∀ r → hoistᴿ V σ r ≡ hoistᴿ V σ' r
  ⌊≗⌋ʰ p (succ V)    = ⌊≗⌋ʰ p V
  ⌊≗⌋ʰ p ⦉ V , W ⦊    = pairʰ-cong (⌊≗⌋ʰ p V) (⌊≗⌋ʰ p W)
  ⌊≗⌋ʰ p (inl V)     = ⌊≗⌋ʰ p V
  ⌊≗⌋ʰ p (inr V)     = ⌊≗⌋ʰ p V
  ⌊≗⌋ʰ p (cons V W)  = pairʰ-cong (⌊≗⌋ʰ p V) (⌊≗⌋ʰ p W)
  ⌊≗⌋ʰ p (cmp ⋈ V W) = cmpʰ-cong (⌊≗⌋ʰ p V) (⌊≗⌋ʰ p W) (⌊≗⌋ᵇ p V) (⌊≗⌋ᵇ p W)
  ⌊≗⌋ʰ p (V ⦂ᵛ A)    = ⌊≗⌋ʰ p V
  ⌊≗⌋ʰ p (var i)     r = refl
  ⌊≗⌋ʰ p (const B c) r = refl
  ⌊≗⌋ʰ p ⋆           r = refl
  ⌊≗⌋ʰ p true        r = refl
  ⌊≗⌋ʰ p false       r = refl
  ⌊≗⌋ʰ p zero        r = refl
  ⌊≗⌋ʰ p nil         r = refl
  ⌊≗⌋ʰ p (lam M)     r = refl
  ⌊≗⌋ʰ p (handler N H) r = refl

  ⌊≗⌋ᵇ : ∀ {Θ n} {σ σ' : DInst Θ} → σ ≗ᴰ σ' → (V : RawV Θ n)
       → ∀ r e → buildᴿ V σ r e ≡ buildᴿ V σ' r e
  ⌊≗⌋ᵇ p (var i)     r e = refl
  ⌊≗⌋ᵇ p (const B c) r e = refl
  ⌊≗⌋ᵇ p ⋆           r e = refl
  ⌊≗⌋ᵇ p true        r e = refl
  ⌊≗⌋ᵇ p false       r e = refl
  ⌊≗⌋ᵇ p zero        r e = refl
  ⌊≗⌋ᵇ p (succ V)    r e = cong succ (⌊≗⌋ᵇ p V r e)
  ⌊≗⌋ᵇ p ⦉ V , W ⦊    r e = cong₂ ⦉_,_⦊ (⌊≗⌋ᵇ p V r (leftᴱ e)) (⌊≗⌋ᵇ p W r (rightᴱ e))
  ⌊≗⌋ᵇ p (inl V)     r e = cong inl (⌊≗⌋ᵇ p V r e)
  ⌊≗⌋ᵇ p (inr V)     r e = cong inr (⌊≗⌋ᵇ p V r e)
  ⌊≗⌋ᵇ p nil         r e = refl
  ⌊≗⌋ᵇ p (cons V W)  r e = cong₂ cons (⌊≗⌋ᵇ p V r (leftᴱ e)) (⌊≗⌋ᵇ p W r (rightᴱ e))
  ⌊≗⌋ᵇ p (cmp ⋈ V W) r e = refl
  ⌊≗⌋ᵇ p (lam M)     r e = cong lam (⌊≗⌋ᵉ p M (extᴿ r))
  ⌊≗⌋ᵇ p (handler N H) r e = refl
  ⌊≗⌋ᵇ p (V ⦂ᵛ A)    r e = ⌊≗⌋ᵇ p V r e

  ⌊≗⌋ᵉ : ∀ {Θ n} {σ σ' : DInst Θ} → σ ≗ᴰ σ' → (M : RawC Θ n)
       → ∀ r → elabᶜ M σ r ≡ elabᶜ M σ' r
  ⌊≗⌋ᵉ p (return V) =
    on₁ᴿ-cong (⌊≗⌋ʰ p V) (λ r e → cong return (⌊≗⌋ᵇ p V r e))
  ⌊≗⌋ᵉ p (M ⨟ N) r = cong₂ _⨟_ (⌊≗⌋ᵉ p M r) (⌊≗⌋ᵉ p N (extᴿ r))
  ⌊≗⌋ᵉ p (V · W) =
    on₁ᴿ-cong (pairʰ-cong (⌊≗⌋ʰ p V) (⌊≗⌋ʰ p W))
              (λ r e → cong₂ _·_ (⌊≗⌋ᵇ p V r (leftᴱ e)) (⌊≗⌋ᵇ p W r (rightᴱ e)))
  ⌊≗⌋ᵉ p (match V `in M) =
    on₁ᴿ-cong (⌊≗⌋ʰ p V)
              (λ r e → cong₂ match_`in_ (⌊≗⌋ᵇ p V r e) (⌊≗⌋ᵉ p M (extᴿ (extᴿ r))))
  ⌊≗⌋ᵉ p (absurd V) =
    on₁ᴿ-cong (⌊≗⌋ʰ p V) (λ r e → cong absurd (⌊≗⌋ᵇ p V r e))
  ⌊≗⌋ᵉ p (if V `then M `else N) =
    on₁ᴿ-cong (⌊≗⌋ʰ p V)
              (λ r e → cong₃ if_`then_`else_ (⌊≗⌋ᵇ p V r e) (⌊≗⌋ᵉ p M r) (⌊≗⌋ᵉ p N r))
  ⌊≗⌋ᵉ p (caseℕ V `zero M `succ N) =
    on₁ᴿ-cong (⌊≗⌋ʰ p V)
              (λ r e → cong₃ caseℕ_`zero_`succ_ (⌊≗⌋ᵇ p V r e) (⌊≗⌋ᵉ p M r)
                                                (⌊≗⌋ᵉ p N (extᴿ r)))
  ⌊≗⌋ᵉ p (case+ V `inl M `inr N) =
    on₁ᴿ-cong (⌊≗⌋ʰ p V)
              (λ r e → cong₃ case+_`inl_`inr_ (⌊≗⌋ᵇ p V r e) (⌊≗⌋ᵉ p M (extᴿ r))
                                              (⌊≗⌋ᵉ p N (extᴿ r)))
  ⌊≗⌋ᵉ p (recℕ V M N) =
    on₁ᴿ-cong (⌊≗⌋ʰ p V)
              (λ r e → cong₃ recℕ (⌊≗⌋ᵇ p V r e) (⌊≗⌋ᵉ p M r) (⌊≗⌋ᵉ p N (extᴿ (extᴿ r))))
  ⌊≗⌋ᵉ p (caseL V `nil M `cons N) =
    on₁ᴿ-cong (⌊≗⌋ʰ p V)
              (λ r e → cong₃ caseL_`nil_`cons_ (⌊≗⌋ᵇ p V r e) (⌊≗⌋ᵉ p M r)
                                               (⌊≗⌋ᵉ p N (extᴿ (extᴿ r))))
  ⌊≗⌋ᵉ p (recL V M N) =
    on₁ᴿ-cong (⌊≗⌋ʰ p V)
              (λ r e → cong₃ recL (⌊≗⌋ᵇ p V r e) (⌊≗⌋ᵉ p M r)
                                  (⌊≗⌋ᵉ p N (extᴿ (extᴿ (extᴿ r)))))
  ⌊≗⌋ᵉ p (perform op V M) =
    on₁ᴿ-cong (⌊≗⌋ʰ p V)
              (λ r e → cong₂ (perform op) (⌊≗⌋ᵇ p V r e) (⌊≗⌋ᵉ p M (extᴿ r)))
  ⌊≗⌋ᵉ p (delay τ M) r = cong (delay τ) (⌊≗⌋ᵉ p M r)
  ⌊≗⌋ᵉ p (handle M `with V) r = ⌊≗⌋ᵃ p M V r
  ⌊≗⌋ᵉ p (unbox i N) r = cong (unbox (posᴿ r (toℕ i))) (⌊≗⌋ᵉ p N (extᴿ r))
  ⌊≗⌋ᵉ p (box ρ V N) =
    on₁ᴿ-cong (⌊≗⌋ʰ p V)
              (λ r e → cong₃ box (⟦≗⟧ʳ p ρ) (⌊≗⌋ᵇ p V r e) (⌊≗⌋ᵉ p N (extᴿ r)))
  ⌊≗⌋ᵉ p (M ⦂ᶜ C) r = ⌊≗⌋ᵉ p M r

  ⌊≗⌋ᵃ : ∀ {Θ n} {σ σ' : DInst Θ} → σ ≗ᴰ σ' → (M : RawC Θ n) → (V : RawV Θ n)
       → ∀ r → elabʰ M V σ r ≡ elabʰ M V σ' r
  ⌊≗⌋ᵃ p M (handler N H) r =
    cong₃ (λ x y z → handle x `with y `in z)
          (⌊≗⌋ᵉ p M r)
          (fun-ext (λ op → fun-ext (λ c → ⌊≗⌋ᵉ (≗ᴰ-,ᵉ p c) (H op) (extᴿ (extᴿ r)))))
          (⌊≗⌋ᵉ p N (extᴿ r))
  ⌊≗⌋ᵃ p M (var i) r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M (const B c) r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M ⋆ r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M true r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M false r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M zero r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M (succ U) r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M ⦉ U , U' ⦊ r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M (inl U) r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M (inr U) r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M nil r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M (cons U U') r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M (cmp ⋈ U U') r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M (lam L) r = ⌊≗⌋ᵉ p M r
  ⌊≗⌋ᵃ p M (U ⦂ᵛ A) r = ⌊≗⌋ᵉ p M r

⌊≗⌋ᴿᶜ : ∀ {Θ n} {σ σ' : DInst Θ} → σ ≗ᴰ σ' → (M : RawC Θ n) → ⌊ M ⌋ᴿᶜ σ ≡ ⌊ M ⌋ᴿᶜ σ'
⌊≗⌋ᴿᶜ p M = ⌊≗⌋ᵉ p M idᴿ

-- Substitution: the term `X [ δ ]` at `σ` is `X` at the composite
-- `δ ⨟ᴰ σ`

mutual

  ⌊[]⌋ʰ : ∀ {Θ Θ' n} → (V : RawV Θ n) → (δ : Subst Θ Θ') → (σ : DInst Θ')
        → ∀ r → hoistᴿ (V [ δ ]ᴿᵛ) σ r ≡ hoistᴿ V (δ ⨟ᴰ σ) r
  ⌊[]⌋ʰ (succ V)    δ σ = ⌊[]⌋ʰ V δ σ
  ⌊[]⌋ʰ ⦉ V , W ⦊    δ σ = pairʰ-cong (⌊[]⌋ʰ V δ σ) (⌊[]⌋ʰ W δ σ)
  ⌊[]⌋ʰ (inl V)     δ σ = ⌊[]⌋ʰ V δ σ
  ⌊[]⌋ʰ (inr V)     δ σ = ⌊[]⌋ʰ V δ σ
  ⌊[]⌋ʰ (cons V W)  δ σ = pairʰ-cong (⌊[]⌋ʰ V δ σ) (⌊[]⌋ʰ W δ σ)
  ⌊[]⌋ʰ (cmp ⋈ V W) δ σ =
    cmpʰ-cong (⌊[]⌋ʰ V δ σ) (⌊[]⌋ʰ W δ σ) (⌊[]⌋ᵇ V δ σ) (⌊[]⌋ᵇ W δ σ)
  ⌊[]⌋ʰ (V ⦂ᵛ A)    δ σ = ⌊[]⌋ʰ V δ σ
  ⌊[]⌋ʰ (var i)     δ σ r = refl
  ⌊[]⌋ʰ (const B c) δ σ r = refl
  ⌊[]⌋ʰ ⋆           δ σ r = refl
  ⌊[]⌋ʰ true        δ σ r = refl
  ⌊[]⌋ʰ false       δ σ r = refl
  ⌊[]⌋ʰ zero        δ σ r = refl
  ⌊[]⌋ʰ nil         δ σ r = refl
  ⌊[]⌋ʰ (lam M)     δ σ r = refl
  ⌊[]⌋ʰ (handler N H) δ σ r = refl

  ⌊[]⌋ᵇ : ∀ {Θ Θ' n} → (V : RawV Θ n) → (δ : Subst Θ Θ') → (σ : DInst Θ')
        → ∀ r e → buildᴿ (V [ δ ]ᴿᵛ) σ r e ≡ buildᴿ V (δ ⨟ᴰ σ) r e
  ⌊[]⌋ᵇ (var i)     δ σ r e = refl
  ⌊[]⌋ᵇ (const B c) δ σ r e = refl
  ⌊[]⌋ᵇ ⋆           δ σ r e = refl
  ⌊[]⌋ᵇ true        δ σ r e = refl
  ⌊[]⌋ᵇ false       δ σ r e = refl
  ⌊[]⌋ᵇ zero        δ σ r e = refl
  ⌊[]⌋ᵇ (succ V)    δ σ r e = cong succ (⌊[]⌋ᵇ V δ σ r e)
  ⌊[]⌋ᵇ ⦉ V , W ⦊    δ σ r e = cong₂ ⦉_,_⦊ (⌊[]⌋ᵇ V δ σ r (leftᴱ e)) (⌊[]⌋ᵇ W δ σ r (rightᴱ e))
  ⌊[]⌋ᵇ (inl V)     δ σ r e = cong inl (⌊[]⌋ᵇ V δ σ r e)
  ⌊[]⌋ᵇ (inr V)     δ σ r e = cong inr (⌊[]⌋ᵇ V δ σ r e)
  ⌊[]⌋ᵇ nil         δ σ r e = refl
  ⌊[]⌋ᵇ (cons V W)  δ σ r e = cong₂ cons (⌊[]⌋ᵇ V δ σ r (leftᴱ e)) (⌊[]⌋ᵇ W δ σ r (rightᴱ e))
  ⌊[]⌋ᵇ (cmp ⋈ V W) δ σ r e = refl
  ⌊[]⌋ᵇ (lam M)     δ σ r e = cong lam (⌊[]⌋ᵉ M δ σ (extᴿ r))
  ⌊[]⌋ᵇ (handler N H) δ σ r e = refl
  ⌊[]⌋ᵇ (V ⦂ᵛ A)    δ σ r e = ⌊[]⌋ᵇ V δ σ r e

  ⌊[]⌋ᵉ : ∀ {Θ Θ' n} → (M : RawC Θ n) → (δ : Subst Θ Θ') → (σ : DInst Θ')
        → ∀ r → elabᶜ (M [ δ ]ᴿᶜ) σ r ≡ elabᶜ M (δ ⨟ᴰ σ) r
  ⌊[]⌋ᵉ (return V) δ σ =
    on₁ᴿ-cong (⌊[]⌋ʰ V δ σ) (λ r e → cong return (⌊[]⌋ᵇ V δ σ r e))
  ⌊[]⌋ᵉ (M ⨟ N) δ σ r = cong₂ _⨟_ (⌊[]⌋ᵉ M δ σ r) (⌊[]⌋ᵉ N δ σ (extᴿ r))
  ⌊[]⌋ᵉ (V · W) δ σ =
    on₁ᴿ-cong (pairʰ-cong (⌊[]⌋ʰ V δ σ) (⌊[]⌋ʰ W δ σ))
              (λ r e → cong₂ _·_ (⌊[]⌋ᵇ V δ σ r (leftᴱ e)) (⌊[]⌋ᵇ W δ σ r (rightᴱ e)))
  ⌊[]⌋ᵉ (match V `in M) δ σ =
    on₁ᴿ-cong (⌊[]⌋ʰ V δ σ)
              (λ r e → cong₂ match_`in_ (⌊[]⌋ᵇ V δ σ r e) (⌊[]⌋ᵉ M δ σ (extᴿ (extᴿ r))))
  ⌊[]⌋ᵉ (absurd V) δ σ =
    on₁ᴿ-cong (⌊[]⌋ʰ V δ σ) (λ r e → cong absurd (⌊[]⌋ᵇ V δ σ r e))
  ⌊[]⌋ᵉ (if V `then M `else N) δ σ =
    on₁ᴿ-cong (⌊[]⌋ʰ V δ σ)
              (λ r e → cong₃ if_`then_`else_ (⌊[]⌋ᵇ V δ σ r e) (⌊[]⌋ᵉ M δ σ r)
                                             (⌊[]⌋ᵉ N δ σ r))
  ⌊[]⌋ᵉ (caseℕ V `zero M `succ N) δ σ =
    on₁ᴿ-cong (⌊[]⌋ʰ V δ σ)
              (λ r e → cong₃ caseℕ_`zero_`succ_ (⌊[]⌋ᵇ V δ σ r e) (⌊[]⌋ᵉ M δ σ r)
                                                (⌊[]⌋ᵉ N δ σ (extᴿ r)))
  ⌊[]⌋ᵉ (case+ V `inl M `inr N) δ σ =
    on₁ᴿ-cong (⌊[]⌋ʰ V δ σ)
              (λ r e → cong₃ case+_`inl_`inr_ (⌊[]⌋ᵇ V δ σ r e) (⌊[]⌋ᵉ M δ σ (extᴿ r))
                                              (⌊[]⌋ᵉ N δ σ (extᴿ r)))
  ⌊[]⌋ᵉ (recℕ V M N) δ σ =
    on₁ᴿ-cong (⌊[]⌋ʰ V δ σ)
              (λ r e → cong₃ recℕ (⌊[]⌋ᵇ V δ σ r e) (⌊[]⌋ᵉ M δ σ r)
                                  (⌊[]⌋ᵉ N δ σ (extᴿ (extᴿ r))))
  ⌊[]⌋ᵉ (caseL V `nil M `cons N) δ σ =
    on₁ᴿ-cong (⌊[]⌋ʰ V δ σ)
              (λ r e → cong₃ caseL_`nil_`cons_ (⌊[]⌋ᵇ V δ σ r e) (⌊[]⌋ᵉ M δ σ r)
                                               (⌊[]⌋ᵉ N δ σ (extᴿ (extᴿ r))))
  ⌊[]⌋ᵉ (recL V M N) δ σ =
    on₁ᴿ-cong (⌊[]⌋ʰ V δ σ)
              (λ r e → cong₃ recL (⌊[]⌋ᵇ V δ σ r e) (⌊[]⌋ᵉ M δ σ r)
                                  (⌊[]⌋ᵉ N δ σ (extᴿ (extᴿ (extᴿ r)))))
  ⌊[]⌋ᵉ (perform op V M) δ σ =
    on₁ᴿ-cong (⌊[]⌋ʰ V δ σ)
              (λ r e → cong₂ (perform op) (⌊[]⌋ᵇ V δ σ r e) (⌊[]⌋ᵉ M δ σ (extᴿ r)))
  ⌊[]⌋ᵉ (delay τ M) δ σ r = cong (delay τ) (⌊[]⌋ᵉ M δ σ r)
  ⌊[]⌋ᵉ (handle M `with V) δ σ r = ⌊[]⌋ᵃ M V δ σ r
  ⌊[]⌋ᵉ (unbox i N) δ σ r = cong (unbox (posᴿ r (toℕ i))) (⌊[]⌋ᵉ N δ σ (extᴿ r))
  ⌊[]⌋ᵉ (box ρ V N) δ σ =
    on₁ᴿ-cong (⌊[]⌋ʰ V δ σ)
              (λ r e → cong₃ box (⟦[]⟧ʳ δ σ ρ) (⌊[]⌋ᵇ V δ σ r e) (⌊[]⌋ᵉ N δ σ (extᴿ r)))
  ⌊[]⌋ᵉ (M ⦂ᶜ C) δ σ r = ⌊[]⌋ᵉ M δ σ r

  ⌊[]⌋ᵃ : ∀ {Θ Θ' n} → (M : RawC Θ n) → (V : RawV Θ n) → (δ : Subst Θ Θ')
        → (σ : DInst Θ')
        → ∀ r → elabʰ (M [ δ ]ᴿᶜ) (V [ δ ]ᴿᵛ) σ r ≡ elabʰ M V (δ ⨟ᴰ σ) r
  ⌊[]⌋ᵃ M (handler N H) δ σ r =
    cong₃ (λ x y z → handle x `with y `in z)
          (⌊[]⌋ᵉ M δ σ r)
          (fun-ext (λ op → fun-ext (λ c →
             trans (⌊[]⌋ᵉ (H op) (δ ↑ᵉ) (σ ,ᵉᴰ c) (extᴿ (extᴿ r)))
                   (⌊≗⌋ᵉ (↑ᵉ-⨟ᴰ δ σ c) (H op) (extᴿ (extᴿ r))))))
          (⌊[]⌋ᵉ N δ σ (extᴿ r))
  ⌊[]⌋ᵃ M (var i) δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M (const B c) δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M ⋆ δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M true δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M false δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M zero δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M (succ U) δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M ⦉ U , U' ⦊ δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M (inl U) δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M (inr U) δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M nil δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M (cons U U') δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M (cmp ⋈ U U') δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M (lam L) δ σ r = ⌊[]⌋ᵉ M δ σ r
  ⌊[]⌋ᵃ M (U ⦂ᵛ A) δ σ r = ⌊[]⌋ᵉ M δ σ r

⌊[]⌋ᴿᶜ : ∀ {Θ Θ' n} → (M : RawC Θ n) → (δ : Subst Θ Θ') → (σ : DInst Θ')
       → ⌊ M [ δ ]ᴿᶜ ⌋ᴿᶜ σ ≡ ⌊ M ⌋ᴿᶜ (δ ⨟ᴰ σ)
⌊[]⌋ᴿᶜ M δ σ = ⌊[]⌋ᵉ M δ σ idᴿ

------------------------------------------------------------------------
-- Transport of closed typings, which erasure does not see

castᵛ : ∀ {Γ Γ' A A'} → Γ ≡ Γ' → A ≡ A' → Γ ⊢V⦂ A → Γ' ⊢V⦂ A'
castᵛ refl refl V = V

castᶜ : ∀ {Γ Γ' C C'} → Γ ≡ Γ' → C ≡ C' → Γ ⊢C⦂ C → Γ' ⊢C⦂ C'
castᶜ refl refl M = M

castᵛ-⌊⌋ : ∀ {Γ Γ' A A'} → (p : Γ ≡ Γ') → (q : A ≡ A') → (V : Γ ⊢V⦂ A)
         → CE.⌊ castᵛ p q V ⌋ᵛ ≡ CE.⌊ V ⌋ᵛ
castᵛ-⌊⌋ refl refl V = refl

castᶜ-⌊⌋ : ∀ {Γ Γ' C C'} → (p : Γ ≡ Γ') → (q : C ≡ C') → (M : Γ ⊢C⦂ C)
         → CE.⌊ castᶜ p q M ⌋ᶜ ≡ CE.⌊ M ⌋ᶜ
castᶜ-⌊⌋ refl refl M = refl

------------------------------------------------------------------------
-- The contexts and types of `perform` and of a handler clause

module _ {Θ : Scope} {n : ℕ} (Γ : OCtx Θ n) (σ : DInst Θ) (op : Op) where

  clause-of : Ctx → VType → VType → Ctx
  clause-of Δ P K = Δ ⟨ ⊤ᵣ ⟩ ∷ P ∷ [ mapᵉ (op-grade op) ] K

  module _ (B : OVType Θ) (c : E) where

    -- the clause's context interpreted at the extended instance, the
    -- interpretation of `Γ` replaced by any `Δ` it maps into

    clause-map : ∀ {Δ} → ⟦ Γ ⟧ᶜᵗˣ σ ≼ Δ
               → ⟦ wkᵉ-ctx Γ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                     ∷ [ rconst (mapᵉ (op-grade op)) ]
                         (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ})) ⟧ᶜᵗˣ (σ ,ᵉᴰ c)
                 ≼ Δ ⟨ ⊤ᵣ ⟩ ∷ ⟦ ⌜ param op ⌝ᵍ ⟧ᵛ (σ ,ᵉᴰ c)
                     ∷ [ mapᵉ (op-grade op) ]
                         (⟦ ⌜ arity op ⌝ᵍ ⟧ᵛ (σ ,ᵉᴰ c) ⇒ ⟦ wkᵉ-v B ⟧ᵛ (σ ,ᵉᴰ c) ‼ c)
    clause-map {Δ} ι = ≼-∷ (≼-∷ (≼-⟨⟩ (subst (_≼ Δ) (sym (⟦wkᵉ⟧ᶜᵗˣ σ c Γ)) ι)))

    clause-ctx : ∀ {Δ}
               → Δ ⟨ ⊤ᵣ ⟩ ∷ ⟦ ⌜ param op ⌝ᵍ ⟧ᵛ (σ ,ᵉᴰ c)
                   ∷ [ mapᵉ (op-grade op) ]
                       (⟦ ⌜ arity op ⌝ᵍ ⟧ᵛ (σ ,ᵉᴰ c) ⇒ ⟦ wkᵉ-v B ⟧ᵛ (σ ,ᵉᴰ c) ‼ c)
                 ≡ Δ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ ⟦ B ⟧ᵛ σ ‼ c)
    clause-ctx {Δ} =
      cong₂ (clause-of Δ)
            (⟦⌜ param op ⌝ᵍ⟧ (σ ,ᵉᴰ c))
            (cong₂ (λ (X Y : VType) → X ⇒ Y ‼ c) (⟦⌜ arity op ⌝ᵍ⟧ (σ ,ᵉᴰ c)) (⟦wkᵉ⟧ᵛ σ c B))

    clause-ty : ⟦ wkᵉ-v B ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ})) ⟧ᶜ (σ ,ᵉᴰ c)
                ≡ ⟦ B ⟧ᵛ σ ‼ (op-grade op ·ₑ c)
    clause-ty = cong (_‼ (op-grade op ·ₑ c)) (⟦wkᵉ⟧ᵛ σ c B)

------------------------------------------------------------------------
-- The typing at an instance

-- the var-rule disjunction as the closed rule's side condition

varOK : ∀ {A : VType} {ρ : R} → Eternal A ⊎ (ρ ≾ᵣ uᵣ) → ¬ Eternal A → ρ ≾ᵣ uᵣ
varOK (inj₁ et) ¬et = ⊥-elim (¬et et)
varOK (inj₂ le) ¬et = le

-- What building a value through a map needs: the value is of eternal
-- type, or the map forgets no lock

Buildable : ∀ {Γ Δ} → VType → Γ ≼ Δ → Set
Buildable A ι = Eternal A ⊎ Full ι

private

  ×-buildˡ : ∀ {Γ Δ A B} {ι : Γ ≼ Δ} → Buildable (A |×| B) ι → Buildable A ι
  ×-buildˡ (inj₁ (et |×|ₑ _)) = inj₁ et
  ×-buildˡ (inj₂ f)           = inj₂ f

  ×-buildʳ : ∀ {Γ Δ A B} {ι : Γ ≼ Δ} → Buildable (A |×| B) ι → Buildable B ι
  ×-buildʳ (inj₁ (_ |×|ₑ et)) = inj₁ et
  ×-buildʳ (inj₂ f)           = inj₂ f

  +-buildˡ : ∀ {Γ Δ A B} {ι : Γ ≼ Δ} → Buildable (A |+| B) ι → Buildable A ι
  +-buildˡ (inj₁ (et |+|ₑ _)) = inj₁ et
  +-buildˡ (inj₂ f)           = inj₂ f

  +-buildʳ : ∀ {Γ Δ A B} {ι : Γ ≼ Δ} → Buildable (A |+| B) ι → Buildable B ι
  +-buildʳ (inj₁ (_ |+|ₑ et)) = inj₁ et
  +-buildʳ (inj₂ f)           = inj₂ f

  List-build : ∀ {Γ Δ A} {ι : Γ ≼ Δ} → Buildable (|List| A) ι → Buildable A ι
  List-build (inj₁ (|List|ₑ et)) = inj₁ et
  List-build (inj₂ f)            = inj₂ f

  sub-build : ∀ {Γ Δ A A'} {ι : Γ ≼ Δ} → A <:ᵛ A' → Buildable A' ι → Buildable A ι
  sub-build p (inj₁ et) = inj₁ (<:ᵛ-eternalˡ p et)
  sub-build p (inj₂ f)  = inj₂ f

-- the hoisted comparisons of two values, the second's after the first's

pairᴴ : ∀ {Θ n Δ} {V W : RawV Θ n}
      → (h : Hoisted Δ V) → Hoisted (end h) W → Hoisted Δ ⦉ V , W ⦊
pairᴴ {V = V} h h' = hoisted (tel h ++ᵀ tel h') (wkᵀ V (tel h') (env h) , env h')

mutual

  hoist : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ} {Δ}
        → (σ : DInst Θ) → σ ⊨ᴰ Q
        → (V : Q ∣ Γ ⊢V⦂ A) → ⟦ Γ ⟧ᶜᵗˣ σ ≼ Δ → SecondClassᵛ OE.⌊ V ⌋ᵛ
        → Hoisted Δ OE.⌊ V ⌋ᵛ
  hoist σ s (succ V)    ι c = hoisted (tel h) (env h) where h = hoist σ s V ι c
  hoist σ s ⦉ V , W ⦊    ι c = hoist₂ σ s V W ι c
  hoist σ s (inl V)     ι c = hoisted (tel h) (env h) where h = hoist σ s V ι c
  hoist σ s (inr V)     ι c = hoisted (tel h) (env h) where h = hoist σ s V ι c
  hoist σ s (cons V W)  ι c = hoisted (tel h) (env h) where h = hoist₂ σ s V W ι c
  hoist σ s (cmp ⋈ V W et) ι c =
    hoisted (tel h ▷ cmpᶜ ⋈ (build σ s V ι' (inj₁ et') (proj₁ (env h)) (proj₁ c))
                            (build σ s W ι' (inj₁ et') (proj₂ (env h)) (proj₂ c)) et')
            (_ , Hd)
    where
      h   = hoist₂ σ s V W ι c
      ι'  = ι ⊕ tel h
      et' = sound-⊩ᴱ s et
  hoist σ s (annᵛ A V)  ι c = hoisted (tel h) (env h) where h = hoist σ s V ι c
  hoist σ s (subV V p)  ι c = hoist σ s V ι c
  hoist σ s (var x ok)  ι c = hoisted [] tt
  hoist σ s (const B c') ι c = hoisted [] tt
  hoist σ s ⋆           ι c = hoisted [] tt
  hoist σ s true        ι c = hoisted [] tt
  hoist σ s false       ι c = hoisted [] tt
  hoist σ s zero        ι c = hoisted [] tt
  hoist σ s nil         ι c = hoisted [] tt
  hoist σ s (lam M)     ι c = hoisted [] tt
  hoist σ s (handler N H) ι ()

  hoist₂ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A B : OVType Θ} {Δ}
         → (σ : DInst Θ) → σ ⊨ᴰ Q
         → (V : Q ∣ Γ ⊢V⦂ A) → (W : Q ∣ Γ ⊢V⦂ B) → ⟦ Γ ⟧ᶜᵗˣ σ ≼ Δ
         → SecondClassᵛ OE.⌊ V ⌋ᵛ × SecondClassᵛ OE.⌊ W ⌋ᵛ
         → Hoisted Δ ⦉ OE.⌊ V ⌋ᵛ , OE.⌊ W ⌋ᵛ ⦊
  hoist₂ σ s V W ι (c , c') = pairᴴ h (hoist σ s W (ι ⊕ tel h) c')
    where h = hoist σ s V ι c

  -- a value at the end of its hoisted comparisons, each read off its
  -- outcome variable

  build : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ} {Δ}
        → (σ : DInst Θ) → σ ⊨ᴰ Q
        → (V : Q ∣ Γ ⊢V⦂ A) → (ι : ⟦ Γ ⟧ᶜᵗˣ σ ≼ Δ) → Buildable (⟦ A ⟧ᵛ σ) ι
        → Envᶜ Δ OE.⌊ V ⌋ᵛ → SecondClassᵛ OE.⌊ V ⌋ᵛ
        → Δ ⊢V⦂ ⟦ A ⟧ᵛ σ
  build σ s (var x ok) ι (inj₁ et) e c =
    var (λ ¬et → ⊥-elim (¬et et)) (proj₂ (lookᴱ ι ⟦ x ⟧ˣ))
  build σ s (var x ok) ι (inj₂ f) e c =
    var (λ ¬et → ≾ᵣ-trans (proj₂ (proj₂ l)) (varOK (sound-VarOK s ok) ¬et))
        (proj₁ (proj₂ l))
    where l = look ι f ⟦ x ⟧ˣ
  build σ s (const B c')   ι b e c        = const c'
  build σ s ⋆              ι b e c        = ⋆
  build σ s true           ι b e c        = true
  build σ s false          ι b e c        = false
  build σ s zero           ι b e c        = zero
  build σ s (succ V)       ι b e c        = succ (build σ s V ι b e c)
  build σ s ⦉ V , W ⦊       ι b (e , e') c =
    ⦉ build σ s V ι (×-buildˡ {ι = ι} b) e (proj₁ c)
    , build σ s W ι (×-buildʳ {ι = ι} b) e' (proj₂ c) ⦊
  build σ s (inl V)        ι b e c        = inl (build σ s V ι (+-buildˡ {ι = ι} b) e c)
  build σ s (inr V)        ι b e c        = inr (build σ s V ι (+-buildʳ {ι = ι} b) e c)
  build σ s nil            ι b e c        = nil
  build σ s (cons V W)     ι b (e , e') c =
    cons (build σ s V ι (List-build {ι = ι} b) e (proj₁ c)) (build σ s W ι b e' (proj₂ c))
  build σ s (cmp ⋈ V W et) ι b (_ , x) c  = var (λ ¬et → ⊥-elim (¬et Boolₑ)) x
  build σ s (lam M)        ι (inj₂ f) e c = lam (instᶜ σ s M (≼-∷ ι) f c)
  build σ s (handler N H)  ι b e ()
  build σ s (annᵛ A V)     ι b e c        = build σ s V ι b e c
  build σ s (subV V p)     ι b e c        =
    subV (build σ s V ι (sub-build {ι = ι} (sound-<:ᵛ s p) b) e c) (sound-<:ᵛ s p)

  instᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ} {Δ}
        → (σ : DInst Θ) → σ ⊨ᴰ Q
        → (M : Q ∣ Γ ⊢C⦂ C) → (ι : ⟦ Γ ⟧ᶜᵗˣ σ ≼ Δ) → Full ι
        → SecondClassᶜ OE.⌊ M ⌋ᶜ
        → Δ ⊢C⦂ ⟦ C ⟧ᶜ σ
  instᶜ σ s (return V) ι f c =
    wrap (tel h) (return (build σ s V (ι ⊕ tel h) (inj₂ (Full-⊕ ι (tel h) f)) (env h) c))
    where h = hoist σ s V ι c
  instᶜ σ s (M ⨟ N) ι f (c , c') = instᶜ σ s M ι f c ⨟ instᶜ σ s N (≼-∷ (≼-⟨⟩ ι)) f c'
  instᶜ σ s (V · W) ι f c =
    wrap (tel h) (build σ s V ι' (inj₂ f') (proj₁ (env h)) (proj₁ c)
                  · build σ s W ι' (inj₂ f') (proj₂ (env h)) (proj₂ c))
    where
      h  = hoist₂ σ s V W ι c
      ι' = ι ⊕ tel h
      f' = Full-⊕ ι (tel h) f
  instᶜ σ s (match V `in M) ι f (c , c') =
    wrap (tel h) (match build σ s V ι' (inj₂ f') (env h) c
                  `in instᶜ σ s M (≼-∷ (≼-∷ ι')) f' c')
    where
      h  = hoist σ s V ι c
      ι' = ι ⊕ tel h
      f' = Full-⊕ ι (tel h) f
  instᶜ σ s (absurd V) ι f c =
    wrap (tel h) (absurd (build σ s V ι' (inj₂ f') (env h) c))
    where
      h  = hoist σ s V ι c
      ι' = ι ⊕ tel h
      f' = Full-⊕ ι (tel h) f
  instᶜ σ s (if V `then M `else N) ι f (c , c' , c'') =
    wrap (tel h) (if build σ s V ι' (inj₂ f') (env h) c
                  `then instᶜ σ s M ι' f' c' `else instᶜ σ s N ι' f' c'')
    where
      h  = hoist σ s V ι c
      ι' = ι ⊕ tel h
      f' = Full-⊕ ι (tel h) f
  instᶜ σ s (caseℕ V `zero M `succ N) ι f (c , c' , c'') =
    wrap (tel h) (caseℕ build σ s V ι' (inj₂ f') (env h) c
                  `zero instᶜ σ s M ι' f' c' `succ instᶜ σ s N (≼-∷ ι') f' c'')
    where
      h  = hoist σ s V ι c
      ι' = ι ⊕ tel h
      f' = Full-⊕ ι (tel h) f
  instᶜ σ s (case+ V `inl M `inr N) ι f (c , c' , c'') =
    wrap (tel h) (case+ build σ s V ι' (inj₂ f') (env h) c
                  `inl instᶜ σ s M (≼-∷ ι') f' c' `inr instᶜ σ s N (≼-∷ ι') f' c'')
    where
      h  = hoist σ s V ι c
      ι' = ι ⊕ tel h
      f' = Full-⊕ ι (tel h) f
  instᶜ σ s (caseL V `nil M `cons N) ι f (c , c' , c'') =
    wrap (tel h) (caseL build σ s V ι' (inj₂ f') (env h) c
                  `nil instᶜ σ s M ι' f' c' `cons instᶜ σ s N (≼-∷ (≼-∷ ι')) f' c'')
    where
      h  = hoist σ s V ι c
      ι' = ι ⊕ tel h
      f' = Full-⊕ ι (tel h) f
  instᶜ σ s (recℕ V M N p) ι f (c , c' , c'') =
    wrap (tel h) (recℕ (build σ s V ι' (inj₂ f') (env h) c) (instᶜ σ s M ι' f' c')
                       (instᶜ σ s N (≼-∷ (≼-⟨⟩ (≼-∷ (≼-⟨⟩ ι')))) f' c'') (sound-≾ₑ s p))
    where
      h  = hoist σ s V ι c
      ι' = ι ⊕ tel h
      f' = Full-⊕ ι (tel h) f
  instᶜ σ s (recL V M N p) ι f (c , c' , c'') =
    wrap (tel h) (recL (build σ s V ι' (inj₂ f') (env h) c) (instᶜ σ s M ι' f' c')
                       (instᶜ σ s N (≼-∷ (≼-⟨⟩ (≼-∷ (≼-∷ (≼-⟨⟩ ι'))))) f' c'') (sound-≾ₑ s p))
    where
      h  = hoist σ s V ι c
      ι' = ι ⊕ tel h
      f' = Full-⊕ ι (tel h) f
  instᶜ σ s (perform op V M) ι f (c , c') =
    wrap (tel h)
      (perform op (castᵛ refl (⟦⌜ param op ⌝ᵍ⟧ σ) (build σ s V ι' (inj₂ f') (env h) c))
                  (castᶜ (cong (end h ⟨ mapᵉ (op-grade op) ⟩ ∷_) (⟦⌜ arity op ⌝ᵍ⟧ σ)) refl
                         (instᶜ σ s M (≼-∷ (≼-⟨⟩ ι')) f' c')))
    where
      h  = hoist σ s V ι c
      ι' = ι ⊕ tel h
      f' = Full-⊕ ι (tel h) f
  instᶜ σ s (delay τ M) ι f c = delay τ (instᶜ σ s M (≼-⟨⟩ ι) f c)
  instᶜ σ s (handle M `with V) ι f c = instʰ σ s M V (<:̂ᵛ-refl _) ι f c
  instᶜ σ s (unbox x p q N) ι f c =
    unbox (proj₁ (proj₂ l)) (≾ᵣ-trans (proj₂ (proj₂ l)) (sound-≾ᵣ s p)) (sound-<:ᵛ s q)
          (instᶜ σ s N (≼-∷ ι) f c)
    where l = look ι f ⟦ x ⟧ˣ
  instᶜ σ s (box ρ V N) ι f (c , c') =
    wrap (tel h) (box (⟦ ρ ⟧ʳ σ) (build σ s V (≼-⟨⟩ ι') (inj₂ f') (lockᴱ OE.⌊ V ⌋ᵛ (env h)) c)
                      (instᶜ σ s N (≼-∷ ι') f' c'))
    where
      h  = hoist σ s V (≼-drop ι) c
      ι' = ι ⊕ tel h
      f' = Full-⊕ ι (tel h) f
  instᶜ σ s (annᶜ C M) ι f c = instᶜ σ s M ι f c
  instᶜ σ s (subC M p) ι f c = subC (instᶜ σ s M ι f c) (sound-<:ᶜ s p)

  -- `handle M with V`, `V` at a subtype of the handler type it is used
  -- at: `V` is a handler under subsumptions. The handled computation is
  -- taken to the handler's handled type, its effect kept; the handler's
  -- return clause is typed under the lock of that effect, which lies
  -- below its own; and the result is taken to the type used.

  instʰ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A X Y : OVType Θ} {ε ε' : EExp Θ} {Δ}
        → (σ : DInst Θ) → σ ⊨ᴰ Q
        → (M : Q ∣ Γ ⊢C⦂ X ‼ ε) → (V : Q ∣ Γ ⊢V⦂ A) → Q ∣ A <:̂ᵛ (X ‼ ε) ⇛ (Y ‼ ε')
        → (ι : ⟦ Γ ⟧ᶜᵗˣ σ ≼ Δ) → Full ι
        → SecondClassᶜ (handle OE.⌊ M ⌋ᶜ `with OE.⌊ V ⌋ᵛ)
        → Δ ⊢C⦂ ⟦ Y ‼ (ε ·̂ₑ ε') ⟧ᶜ σ
  instʰ {Γ = Γ} σ s M (handler {B = B₀} N H) ((pX ‼ₛ pε) ⇛ₛ (pY ‼ₛ pε')) ι f
        (c , c' , c'') =
    subC (handle (subC (instᶜ σ s M ι f c) (sound-<:ᵛ s pX ‼ₛ ≾ₑ-refl))
            `with (λ op e → castᶜ (clause-ctx Γ σ op B₀ e) (clause-ty Γ σ op B₀ e)
                               (instᶜ (σ ,ᵉᴰ e) (⊨ᴰ-,ᵉ e s) (H op) (clause-map Γ σ op B₀ e ι)
                                      (Full-subst (sym (⟦wkᵉ⟧ᶜᵗˣ σ e Γ)) ι f) (c'' op)))
            `in (instᶜ σ s N (≼-∷ (≼-≾ ι (map-monotoneᵉ (sound-≾ₑ s pε)))) f c'))
         (sound-<:ᵛ s pY ‼ₛ ·ₑ-monoʳ-≾ₑ (sound-≾ₑ s pε'))
  instʰ σ s M (subV V p) q ι f c = instʰ σ s M V (<:̂ᵛ-trans p q) ι f c
  instʰ σ s M (var x ok) q ι f ()
  instʰ σ s M (const B c') q ι f ()
  instʰ σ s M ⋆ q ι f ()
  instʰ σ s M true q ι f ()
  instʰ σ s M false q ι f ()
  instʰ σ s M zero q ι f ()
  instʰ σ s M (succ V) q ι f ()
  instʰ σ s M ⦉ V , W ⦊ q ι f ()
  instʰ σ s M (inl V) q ι f ()
  instʰ σ s M (inr V) q ι f ()
  instʰ σ s M nil q ι f ()
  instʰ σ s M (cons V W) q ι f ()
  instʰ σ s M (cmp ⋈ V W et) q ι f ()
  instʰ σ s M (lam L) q ι f ()
  instʰ σ s M (annᵛ A V) q ι f ()

------------------------------------------------------------------------
-- The typing is of the elaboration

-- the erasure of hoisted comparisons, through the raw map of the maps

pairᴴ-⌊⌋ : ∀ {Θ n Γ Δ} {V W : RawV Θ n} (ι : Γ ≼ Δ)
         → (h : Hoisted Δ V) → (h' : Hoisted (end h) W)
         → (f g : RMap → RTel × Envᴿ)
         → ⌊ h ⌋ʰ ≡ f ⌊ ι ⌋ᵐ → ⌊ h' ⌋ʰ ≡ g (⌊ ι ⌋ᵐ ⊕ᴿ ⌊ tel h ⌋ᵀ)
         → ⌊ pairᴴ h h' ⌋ʰ ≡ pairʰ f g ⌊ ι ⌋ᵐ
pairᴴ-⌊⌋ {V = V} {W} ι h h' f g e e' =
  trans (cong₂ _,_ (⌊++⌋ᵀ (tel h) (tel h'))
                   (cong (_⊗ᴿ ⌊ W ⌋ᴱ (env h')) (⌊wkᵀ⌋ V (tel h') (env h))))
        (trans (pairᵗ-at ⌊ h ⌋ʰ (λ _ → ⌊ h' ⌋ʰ) (λ T → g (⌊ ι ⌋ᵐ ⊕ᴿ T)) e')
               (cong (λ p → pairᵗ p (λ T → g (⌊ ι ⌋ᵐ ⊕ᴿ T))) e))

mutual

  hoist-⌊⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ} {Δ}
           → (σ : DInst Θ) → (s : σ ⊨ᴰ Q)
           → (V : Q ∣ Γ ⊢V⦂ A) → (ι : ⟦ Γ ⟧ᶜᵗˣ σ ≼ Δ) → (c : SecondClassᵛ OE.⌊ V ⌋ᵛ)
           → ⌊ hoist σ s V ι c ⌋ʰ ≡ hoistᴿ OE.⌊ V ⌋ᵛ σ ⌊ ι ⌋ᵐ
  hoist-⌊⌋ σ s (succ V)    ι c = hoist-⌊⌋ σ s V ι c
  hoist-⌊⌋ σ s ⦉ V , W ⦊    ι c = hoist₂-⌊⌋ σ s V W ι c
  hoist-⌊⌋ σ s (inl V)     ι c = hoist-⌊⌋ σ s V ι c
  hoist-⌊⌋ σ s (inr V)     ι c = hoist-⌊⌋ σ s V ι c
  hoist-⌊⌋ σ s (cons V W)  ι c = hoist₂-⌊⌋ σ s V W ι c
  hoist-⌊⌋ σ s (cmp ⋈ V W et) ι c =
    trans (cong₂ (λ y z → ⌊ tel h ⌋ᵀ ▷ cmpᴿ ⋈ y z , outᴿ 0) ea eb)
          (cong (cmpᵗ ⋈ (buildᴿ OE.⌊ V ⌋ᵛ σ) (buildᴿ OE.⌊ W ⌋ᵛ σ) ⌊ ι ⌋ᵐ)
                (hoist₂-⌊⌋ σ s V W ι c))
    where
      h  = hoist₂ σ s V W ι c
      ι' = ι ⊕ tel h
      b  = inj₁ (sound-⊩ᴱ s et)
      ea = trans (build-⌊⌋ σ s V ι' b (proj₁ (env h)) (proj₁ c))
                 (cong (λ r → buildᴿ OE.⌊ V ⌋ᵛ σ r (⌊ OE.⌊ V ⌋ᵛ ⌋ᴱ (proj₁ (env h))))
                       (⌊⊕⌋ᵐ ι (tel h)))
      eb = trans (build-⌊⌋ σ s W ι' b (proj₂ (env h)) (proj₂ c))
                 (cong (λ r → buildᴿ OE.⌊ W ⌋ᵛ σ r (⌊ OE.⌊ W ⌋ᵛ ⌋ᴱ (proj₂ (env h))))
                       (⌊⊕⌋ᵐ ι (tel h)))
  hoist-⌊⌋ σ s (annᵛ A V)  ι c = hoist-⌊⌋ σ s V ι c
  hoist-⌊⌋ σ s (subV V p)  ι c = hoist-⌊⌋ σ s V ι c
  hoist-⌊⌋ σ s (var x ok)  ι c = refl
  hoist-⌊⌋ σ s (const B c') ι c = refl
  hoist-⌊⌋ σ s ⋆           ι c = refl
  hoist-⌊⌋ σ s true        ι c = refl
  hoist-⌊⌋ σ s false       ι c = refl
  hoist-⌊⌋ σ s zero        ι c = refl
  hoist-⌊⌋ σ s nil         ι c = refl
  hoist-⌊⌋ σ s (lam M)     ι c = refl
  hoist-⌊⌋ σ s (handler N H) ι ()

  hoist₂-⌊⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A B : OVType Θ} {Δ}
            → (σ : DInst Θ) → (s : σ ⊨ᴰ Q)
            → (V : Q ∣ Γ ⊢V⦂ A) → (W : Q ∣ Γ ⊢V⦂ B) → (ι : ⟦ Γ ⟧ᶜᵗˣ σ ≼ Δ)
            → (c : SecondClassᵛ OE.⌊ V ⌋ᵛ × SecondClassᵛ OE.⌊ W ⌋ᵛ)
            → ⌊ hoist₂ σ s V W ι c ⌋ʰ ≡ pairʰ (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoistᴿ OE.⌊ W ⌋ᵛ σ) ⌊ ι ⌋ᵐ
  hoist₂-⌊⌋ σ s V W ι (c , c') =
    pairᴴ-⌊⌋ ι h (hoist σ s W (ι ⊕ tel h) c') (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoistᴿ OE.⌊ W ⌋ᵛ σ)
             (hoist-⌊⌋ σ s V ι c)
             (trans (hoist-⌊⌋ σ s W (ι ⊕ tel h) c')
                    (cong (hoistᴿ OE.⌊ W ⌋ᵛ σ) (⌊⊕⌋ᵐ ι (tel h))))
    where h = hoist σ s V ι c

  build-⌊⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ} {Δ}
           → (σ : DInst Θ) → (s : σ ⊨ᴰ Q)
           → (V : Q ∣ Γ ⊢V⦂ A) → (ι : ⟦ Γ ⟧ᶜᵗˣ σ ≼ Δ) → (b : Buildable (⟦ A ⟧ᵛ σ) ι)
           → (e : Envᶜ Δ OE.⌊ V ⌋ᵛ) → (c : SecondClassᵛ OE.⌊ V ⌋ᵛ)
           → CE.⌊ build σ s V ι b e c ⌋ᵛ ≡ buildᴿ OE.⌊ V ⌋ᵛ σ ⌊ ι ⌋ᵐ (⌊ OE.⌊ V ⌋ᵛ ⌋ᴱ e)
  build-⌊⌋ σ s (var x ok) ι (inj₁ et) e c =
    cong var (trans (lookᴱ-pos ι ⟦ x ⟧ˣ) (cong (posᴿ ⌊ ι ⌋ᵐ) (⟦⟧ˣ-pos x)))
  build-⌊⌋ σ s (var x ok) ι (inj₂ f) e c =
    cong var (trans (look-pos ι f ⟦ x ⟧ˣ) (cong (posᴿ ⌊ ι ⌋ᵐ) (⟦⟧ˣ-pos x)))
  build-⌊⌋ σ s (const B c')   ι b e c        = refl
  build-⌊⌋ σ s ⋆              ι b e c        = refl
  build-⌊⌋ σ s true           ι b e c        = refl
  build-⌊⌋ σ s false          ι b e c        = refl
  build-⌊⌋ σ s zero           ι b e c        = refl
  build-⌊⌋ σ s (succ V)       ι b e c        = cong succ (build-⌊⌋ σ s V ι b e c)
  build-⌊⌋ σ s ⦉ V , W ⦊       ι b (e , e') c =
    cong₂ ⦉_,_⦊ (build-⌊⌋ σ s V ι (×-buildˡ {ι = ι} b) e (proj₁ c))
                (build-⌊⌋ σ s W ι (×-buildʳ {ι = ι} b) e' (proj₂ c))
  build-⌊⌋ σ s (inl V)        ι b e c        = cong inl (build-⌊⌋ σ s V ι (+-buildˡ {ι = ι} b) e c)
  build-⌊⌋ σ s (inr V)        ι b e c        = cong inr (build-⌊⌋ σ s V ι (+-buildʳ {ι = ι} b) e c)
  build-⌊⌋ σ s nil            ι b e c        = refl
  build-⌊⌋ σ s (cons V W)     ι b (e , e') c =
    cong₂ cons (build-⌊⌋ σ s V ι (List-build {ι = ι} b) e (proj₁ c))
               (build-⌊⌋ σ s W ι b e' (proj₂ c))
  build-⌊⌋ σ s (cmp ⋈ V W et) ι b (_ , x) c  = refl
  build-⌊⌋ σ s (lam M)        ι (inj₂ f) e c = cong lam (instᶜ-⌊⌋ σ s M (≼-∷ ι) f c)
  build-⌊⌋ σ s (handler N H)  ι b e ()
  build-⌊⌋ σ s (annᵛ A V)     ι b e c        = build-⌊⌋ σ s V ι b e c
  build-⌊⌋ σ s (subV V p)     ι b e c        =
    build-⌊⌋ σ s V ι (sub-build {ι = ι} (sound-<:ᵛ s p) b) e c

  -- a computation after the comparisons hoisted from its values: the
  -- erasure of its typing at the end of the telescope

  on₁-⌊⌋ : ∀ {Θ n} {V : RawV Θ n} {Γ Δ C} → (ι : Γ ≼ Δ) → (h : Hoisted Δ V)
         → (f : RMap → RTel × Envᴿ) → ⌊ h ⌋ʰ ≡ f ⌊ ι ⌋ᵐ
         → (M : end h ⊢C⦂ C) → (K : RMap → Envᴿ → ErC)
         → CE.⌊ M ⌋ᶜ ≡ K ⌊ ι ⊕ tel h ⌋ᵐ (⌊ V ⌋ᴱ (env h))
         → CE.⌊ wrap (tel h) M ⌋ᶜ ≡ on₁ᴿ f K ⌊ ι ⌋ᵐ
  on₁-⌊⌋ {V = V} ι h f e M K eM =
    trans (⌊wrap⌋ (tel h) M)
          (trans (cong (wrapᴿ ⌊ tel h ⌋ᵀ)
                       (trans eM (cong (λ r → K r (⌊ V ⌋ᴱ (env h))) (⌊⊕⌋ᵐ ι (tel h)))))
                 (cong (on₁ᵗ K ⌊ ι ⌋ᵐ) e))

  instᶜ-⌊⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ} {Δ}
           → (σ : DInst Θ) → (s : σ ⊨ᴰ Q)
           → (M : Q ∣ Γ ⊢C⦂ C) → (ι : ⟦ Γ ⟧ᶜᵗˣ σ ≼ Δ) → (f : Full ι)
           → (c : SecondClassᶜ OE.⌊ M ⌋ᶜ)
           → CE.⌊ instᶜ σ s M ι f c ⌋ᶜ ≡ elabᶜ OE.⌊ M ⌋ᶜ σ ⌊ ι ⌋ᵐ
  instᶜ-⌊⌋ σ s (return V) ι f c =
    on₁-⌊⌋ ι h (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoist-⌊⌋ σ s V ι c) _
      (λ r e → return (buildᴿ OE.⌊ V ⌋ᵛ σ r e))
           (cong return (build-⌊⌋ σ s V (ι ⊕ tel h) (inj₂ f') (env h) c))
    where
      h  = hoist σ s V ι c
      f' = Full-⊕ ι (tel h) f
  instᶜ-⌊⌋ σ s (M ⨟ N) ι f (c , c') =
    cong₂ _⨟_ (instᶜ-⌊⌋ σ s M ι f c) (instᶜ-⌊⌋ σ s N (≼-∷ (≼-⟨⟩ ι)) f c')
  instᶜ-⌊⌋ σ s (V · W) ι f c =
    on₁-⌊⌋ ι h (pairʰ (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoistᴿ OE.⌊ W ⌋ᵛ σ)) (hoist₂-⌊⌋ σ s V W ι c) _
      (λ r e → buildᴿ OE.⌊ V ⌋ᵛ σ r (leftᴱ e) · buildᴿ OE.⌊ W ⌋ᵛ σ r (rightᴱ e))
           (cong₂ _·_ (build-⌊⌋ σ s V (ι ⊕ tel h) (inj₂ f') (proj₁ (env h)) (proj₁ c))
                      (build-⌊⌋ σ s W (ι ⊕ tel h) (inj₂ f') (proj₂ (env h)) (proj₂ c)))
    where
      h  = hoist₂ σ s V W ι c
      f' = Full-⊕ ι (tel h) f
  instᶜ-⌊⌋ σ s (match V `in M) ι f (c , c') =
    on₁-⌊⌋ ι h (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoist-⌊⌋ σ s V ι c) _
      (λ r e → match buildᴿ OE.⌊ V ⌋ᵛ σ r e `in elabᶜ OE.⌊ M ⌋ᶜ σ (extᴿ (extᴿ r)))
           (cong₂ match_`in_ (build-⌊⌋ σ s V (ι ⊕ tel h) (inj₂ f') (env h) c)
                             (instᶜ-⌊⌋ σ s M (≼-∷ (≼-∷ (ι ⊕ tel h))) f' c'))
    where
      h  = hoist σ s V ι c
      f' = Full-⊕ ι (tel h) f
  instᶜ-⌊⌋ σ s (absurd V) ι f c =
    on₁-⌊⌋ ι h (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoist-⌊⌋ σ s V ι c) _
      (λ r e → absurd (buildᴿ OE.⌊ V ⌋ᵛ σ r e))
           (cong absurd (build-⌊⌋ σ s V (ι ⊕ tel h) (inj₂ f') (env h) c))
    where
      h  = hoist σ s V ι c
      f' = Full-⊕ ι (tel h) f
  instᶜ-⌊⌋ σ s (if V `then M `else N) ι f (c , c' , c'') =
    on₁-⌊⌋ ι h (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoist-⌊⌋ σ s V ι c) _
      (λ r e → if buildᴿ OE.⌊ V ⌋ᵛ σ r e `then elabᶜ OE.⌊ M ⌋ᶜ σ r `else elabᶜ OE.⌊ N ⌋ᶜ σ r)
           (cong₃ if_`then_`else_ (build-⌊⌋ σ s V (ι ⊕ tel h) (inj₂ f') (env h) c)
                                  (instᶜ-⌊⌋ σ s M (ι ⊕ tel h) f' c')
                                  (instᶜ-⌊⌋ σ s N (ι ⊕ tel h) f' c''))
    where
      h  = hoist σ s V ι c
      f' = Full-⊕ ι (tel h) f
  instᶜ-⌊⌋ σ s (caseℕ V `zero M `succ N) ι f (c , c' , c'') =
    on₁-⌊⌋ ι h (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoist-⌊⌋ σ s V ι c) _
      (λ r e → caseℕ buildᴿ OE.⌊ V ⌋ᵛ σ r e `zero elabᶜ OE.⌊ M ⌋ᶜ σ r `succ elabᶜ OE.⌊ N ⌋ᶜ σ (extᴿ r))
           (cong₃ caseℕ_`zero_`succ_ (build-⌊⌋ σ s V (ι ⊕ tel h) (inj₂ f') (env h) c)
                                     (instᶜ-⌊⌋ σ s M (ι ⊕ tel h) f' c')
                                     (instᶜ-⌊⌋ σ s N (≼-∷ (ι ⊕ tel h)) f' c''))
    where
      h  = hoist σ s V ι c
      f' = Full-⊕ ι (tel h) f
  instᶜ-⌊⌋ σ s (case+ V `inl M `inr N) ι f (c , c' , c'') =
    on₁-⌊⌋ ι h (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoist-⌊⌋ σ s V ι c) _
      (λ r e → case+ buildᴿ OE.⌊ V ⌋ᵛ σ r e `inl elabᶜ OE.⌊ M ⌋ᶜ σ (extᴿ r) `inr elabᶜ OE.⌊ N ⌋ᶜ σ (extᴿ r))
           (cong₃ case+_`inl_`inr_ (build-⌊⌋ σ s V (ι ⊕ tel h) (inj₂ f') (env h) c)
                                   (instᶜ-⌊⌋ σ s M (≼-∷ (ι ⊕ tel h)) f' c')
                                   (instᶜ-⌊⌋ σ s N (≼-∷ (ι ⊕ tel h)) f' c''))
    where
      h  = hoist σ s V ι c
      f' = Full-⊕ ι (tel h) f
  instᶜ-⌊⌋ σ s (caseL V `nil M `cons N) ι f (c , c' , c'') =
    on₁-⌊⌋ ι h (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoist-⌊⌋ σ s V ι c) _
      (λ r e → caseL buildᴿ OE.⌊ V ⌋ᵛ σ r e `nil elabᶜ OE.⌊ M ⌋ᶜ σ r `cons elabᶜ OE.⌊ N ⌋ᶜ σ (extᴿ (extᴿ r)))
           (cong₃ caseL_`nil_`cons_ (build-⌊⌋ σ s V (ι ⊕ tel h) (inj₂ f') (env h) c)
                                    (instᶜ-⌊⌋ σ s M (ι ⊕ tel h) f' c')
                                    (instᶜ-⌊⌋ σ s N (≼-∷ (≼-∷ (ι ⊕ tel h))) f' c''))
    where
      h  = hoist σ s V ι c
      f' = Full-⊕ ι (tel h) f
  instᶜ-⌊⌋ σ s (recℕ V M N p) ι f (c , c' , c'') =
    on₁-⌊⌋ ι h (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoist-⌊⌋ σ s V ι c) _
      (λ r e → recℕ (buildᴿ OE.⌊ V ⌋ᵛ σ r e) (elabᶜ OE.⌊ M ⌋ᶜ σ r) (elabᶜ OE.⌊ N ⌋ᶜ σ (extᴿ (extᴿ r))))
           (cong₃ recℕ (build-⌊⌋ σ s V (ι ⊕ tel h) (inj₂ f') (env h) c)
                       (instᶜ-⌊⌋ σ s M (ι ⊕ tel h) f' c')
                       (instᶜ-⌊⌋ σ s N (≼-∷ (≼-⟨⟩ (≼-∷ (≼-⟨⟩ (ι ⊕ tel h))))) f' c''))
    where
      h  = hoist σ s V ι c
      f' = Full-⊕ ι (tel h) f
  instᶜ-⌊⌋ σ s (recL V M N p) ι f (c , c' , c'') =
    on₁-⌊⌋ ι h (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoist-⌊⌋ σ s V ι c) _
      (λ r e → recL (buildᴿ OE.⌊ V ⌋ᵛ σ r e) (elabᶜ OE.⌊ M ⌋ᶜ σ r) (elabᶜ OE.⌊ N ⌋ᶜ σ (extᴿ (extᴿ (extᴿ r)))))
           (cong₃ recL (build-⌊⌋ σ s V (ι ⊕ tel h) (inj₂ f') (env h) c)
                       (instᶜ-⌊⌋ σ s M (ι ⊕ tel h) f' c')
                       (instᶜ-⌊⌋ σ s N (≼-∷ (≼-⟨⟩ (≼-∷ (≼-∷ (≼-⟨⟩ (ι ⊕ tel h)))))) f' c''))
    where
      h  = hoist σ s V ι c
      f' = Full-⊕ ι (tel h) f
  instᶜ-⌊⌋ σ s (perform op V M) ι f (c , c') =
    on₁-⌊⌋ ι h (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoist-⌊⌋ σ s V ι c) _
      (λ r e → perform op (buildᴿ OE.⌊ V ⌋ᵛ σ r e) (elabᶜ OE.⌊ M ⌋ᶜ σ (extᴿ r)))
           (cong₂ (perform op)
                  (trans (castᵛ-⌊⌋ refl (⟦⌜ param op ⌝ᵍ⟧ σ) _)
                         (build-⌊⌋ σ s V (ι ⊕ tel h) (inj₂ f') (env h) c))
                  (trans (castᶜ-⌊⌋ (cong (end h ⟨ mapᵉ (op-grade op) ⟩ ∷_) (⟦⌜ arity op ⌝ᵍ⟧ σ))
                                   refl _)
                         (instᶜ-⌊⌋ σ s M (≼-∷ (≼-⟨⟩ (ι ⊕ tel h))) f' c')))
    where
      h  = hoist σ s V ι c
      f' = Full-⊕ ι (tel h) f
  instᶜ-⌊⌋ σ s (delay τ M) ι f c = cong (delay τ) (instᶜ-⌊⌋ σ s M (≼-⟨⟩ ι) f c)
  instᶜ-⌊⌋ σ s (handle M `with V) ι f c = instʰ-⌊⌋ σ s M V (<:̂ᵛ-refl _) ι f c
  instᶜ-⌊⌋ σ s (unbox x p q N) ι f c =
    cong₂ unbox (trans (look-pos ι f ⟦ x ⟧ˣ) (cong (posᴿ ⌊ ι ⌋ᵐ) (⟦⟧ˣ-pos x)))
                (instᶜ-⌊⌋ σ s N (≼-∷ ι) f c)
  instᶜ-⌊⌋ σ s (box ρ V N) ι f (c , c') =
    on₁-⌊⌋ ι h (hoistᴿ OE.⌊ V ⌋ᵛ σ) (hoist-⌊⌋ σ s V (≼-drop ι) c) _
      (λ r e → box (⟦ ρ ⟧ʳ σ) (buildᴿ OE.⌊ V ⌋ᵛ σ r e) (elabᶜ OE.⌊ N ⌋ᶜ σ (extᴿ r)))
           (cong₂ (box (⟦ ρ ⟧ʳ σ))
                  (trans (build-⌊⌋ σ s V (≼-⟨⟩ (ι ⊕ tel h)) (inj₂ f') (lockᴱ OE.⌊ V ⌋ᵛ (env h)) c)
                         (cong (buildᴿ OE.⌊ V ⌋ᵛ σ ⌊ ι ⊕ tel h ⌋ᵐ) (⌊lockᴱ⌋ OE.⌊ V ⌋ᵛ (env h))))
                  (instᶜ-⌊⌋ σ s N (≼-∷ (ι ⊕ tel h)) f' c'))
    where
      h  = hoist σ s V (≼-drop ι) c
      f' = Full-⊕ ι (tel h) f
  instᶜ-⌊⌋ σ s (annᶜ C M) ι f c = instᶜ-⌊⌋ σ s M ι f c
  instᶜ-⌊⌋ σ s (subC M p) ι f c = instᶜ-⌊⌋ σ s M ι f c

  instʰ-⌊⌋ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A X Y : OVType Θ} {ε ε' : EExp Θ} {Δ}
           → (σ : DInst Θ) → (s : σ ⊨ᴰ Q)
           → (M : Q ∣ Γ ⊢C⦂ X ‼ ε) → (V : Q ∣ Γ ⊢V⦂ A)
           → (q : Q ∣ A <:̂ᵛ (X ‼ ε) ⇛ (Y ‼ ε'))
           → (ι : ⟦ Γ ⟧ᶜᵗˣ σ ≼ Δ) → (f : Full ι)
           → (c : SecondClassᶜ (handle OE.⌊ M ⌋ᶜ `with OE.⌊ V ⌋ᵛ))
           → CE.⌊ instʰ σ s M V q ι f c ⌋ᶜ ≡ elabʰ OE.⌊ M ⌋ᶜ OE.⌊ V ⌋ᵛ σ ⌊ ι ⌋ᵐ
  instʰ-⌊⌋ {Γ = Γ} σ s M (handler {B = B₀} N H) ((pX ‼ₛ pε) ⇛ₛ (pY ‼ₛ pε')) ι f
           (c , c' , c'') =
    cong₃ (λ x y z → handle x `with y `in z)
          (instᶜ-⌊⌋ σ s M ι f c)
          (fun-ext λ op → fun-ext λ e →
             trans (castᶜ-⌊⌋ (clause-ctx Γ σ op B₀ e) (clause-ty Γ σ op B₀ e)
                             (instᶜ (σ ,ᵉᴰ e) (⊨ᴰ-,ᵉ e s) (H op) (clause-map Γ σ op B₀ e ι)
                                    (Full-subst (sym (⟦wkᵉ⟧ᶜᵗˣ σ e Γ)) ι f) (c'' op)))
                   (trans (instᶜ-⌊⌋ (σ ,ᵉᴰ e) (⊨ᴰ-,ᵉ e s) (H op) (clause-map Γ σ op B₀ e ι)
                                    (Full-subst (sym (⟦wkᵉ⟧ᶜᵗˣ σ e Γ)) ι f) (c'' op))
                          (cong (λ r → elabᶜ OE.⌊ H op ⌋ᶜ (σ ,ᵉᴰ e) (extᴿ (extᴿ r)))
                                (⌊subst⌋ᵐ (sym (⟦wkᵉ⟧ᶜᵗˣ σ e Γ)) ι))))
          (instᶜ-⌊⌋ σ s N (≼-∷ (≼-≾ ι (map-monotoneᵉ (sound-≾ₑ s pε)))) f c')
  instʰ-⌊⌋ σ s M (subV V p) q ι f c = instʰ-⌊⌋ σ s M V (<:̂ᵛ-trans p q) ι f c
  instʰ-⌊⌋ σ s M (var x ok) q ι f ()
  instʰ-⌊⌋ σ s M (const B c') q ι f ()
  instʰ-⌊⌋ σ s M ⋆ q ι f ()
  instʰ-⌊⌋ σ s M true q ι f ()
  instʰ-⌊⌋ σ s M false q ι f ()
  instʰ-⌊⌋ σ s M zero q ι f ()
  instʰ-⌊⌋ σ s M (succ V) q ι f ()
  instʰ-⌊⌋ σ s M ⦉ V , W ⦊ q ι f ()
  instʰ-⌊⌋ σ s M (inl V) q ι f ()
  instʰ-⌊⌋ σ s M (inr V) q ι f ()
  instʰ-⌊⌋ σ s M nil q ι f ()
  instʰ-⌊⌋ σ s M (cons V W) q ι f ()
  instʰ-⌊⌋ σ s M (cmp ⋈ V W et) q ι f ()
  instʰ-⌊⌋ σ s M (lam L) q ι f ()
  instʰ-⌊⌋ σ s M (annᵛ A V) q ι f ()

------------------------------------------------------------------------
-- The instantiation theorem: an open typing under `Q` of a term whose
-- handlers are second-class is, at every declarative instance
-- satisfying `Q`, a closed typing of the term's elaboration; a value's,
-- of the elaboration of `return V`

instantiateᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
             → (σ : DInst Θ) → σ ⊨ᴰ Q
             → (D : Q ∣ Γ ⊢C⦂ C) → SecondClassᶜ OE.⌊ D ⌋ᶜ
             → Σ[ D' ∈ ⟦ Γ ⟧ᶜᵗˣ σ ⊢C⦂ ⟦ C ⟧ᶜ σ ] (CE.⌊ D' ⌋ᶜ ≡ ⌊ OE.⌊ D ⌋ᶜ ⌋ᴿᶜ σ)
instantiateᶜ σ s D c = instᶜ σ s D ≼-refl tt c , instᶜ-⌊⌋ σ s D ≼-refl tt c

instantiateᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
             → (σ : DInst Θ) → σ ⊨ᴰ Q
             → (D : Q ∣ Γ ⊢V⦂ A) → SecondClassᵛ OE.⌊ D ⌋ᵛ
             → Σ[ D' ∈ ⟦ Γ ⟧ᶜᵗˣ σ ⊢C⦂ ⟦ A ‼ ûₑ ⟧ᶜ σ ] (CE.⌊ D' ⌋ᶜ ≡ ⌊ return OE.⌊ D ⌋ᵛ ⌋ᴿᶜ σ)
instantiateᵛ σ s D c = instantiateᶜ σ s (return D) c

------------------------------------------------------------------------
-- The instantiation theorem in the open syntax: at every closed
-- instance `δ` satisfying `Q`, a closed typing in the translation of
-- the instantiated context and type, through `⌞ δ ⌟ˢ`

instantiateˢᶜ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
              → (δ : Subst Θ ∅ˢ) → δ ⊨ Q ∣ []
              → (D : Q ∣ Γ ⊢C⦂ C) → SecondClassᶜ OE.⌊ D ⌋ᶜ
              → Σ[ D' ∈ ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⊢C⦂ ⌞ C [ δ ]ᶜ ⌟ᶜ ]
                  (CE.⌊ D' ⌋ᶜ ≡ ⌞ OE.⌊ D ⌋ᶜ [ δ ]ᴿᶜ ⌟ᴿᶜ)
instantiateˢᶜ {Γ = Γ} {C = C} δ s D c with instantiateᶜ ⌞ δ ⌟ˢ (⊨→⊨ᴰ s) D c
... | D' , e = castᶜ p q D' , trans (castᶜ-⌊⌋ p q D') (trans e (sym (⌊[]⌋ᴿᶜ OE.⌊ D ⌋ᶜ δ ∅ᴰ)))
  where
    p = sym (⌞[]⌟ᶜᵗˣ δ Γ)
    q = sym (⌞[]⌟ᶜ δ C)

instantiateˢᵛ : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
              → (δ : Subst Θ ∅ˢ) → δ ⊨ Q ∣ []
              → (D : Q ∣ Γ ⊢V⦂ A) → SecondClassᵛ OE.⌊ D ⌋ᵛ
              → Σ[ D' ∈ ⌞ Γ [ δ ]ᶜᵗˣ ⌟ᶜᵗˣ ⊢C⦂ ⌞ (A ‼ ûₑ) [ δ ]ᶜ ⌟ᶜ ]
                  (CE.⌊ D' ⌋ᶜ ≡ ⌞ return OE.⌊ D ⌋ᵛ [ δ ]ᴿᶜ ⌟ᴿᶜ)
instantiateˢᵛ δ s D c = instantiateˢᶜ δ s (return D) c
