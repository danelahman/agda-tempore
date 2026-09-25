------------------------------------------------------------------
-- The constraints generation gives have the shape the invariants --
-- ask for                                                        --
--                                                                --
-- For every raw term, annotated or not: every greater side of an --
-- ordering, and every grade of a type, is a whole unknown or     --
-- mentions only unknowns free in `π`, the program's variables    --
-- and the enclosing clauses' rigids. The fresh unknowns of a     --
-- rule are whole where they are greater, an expected grade is    --
-- passed on or is a clause's bound `op · j`, and an annotation   --
-- is read through `ι`, which lands among `π`'s unknowns.         --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl.Invariants.Generate
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.GroundTypes Grades BTs using (GType)

open import TypeInference.OpenSyntax.Grades         S
open import TypeInference.OpenSyntax.Types          S
open import TypeInference.OpenSyntax.Contexts       S
open import TypeInference.OpenSyntax.ContextsLemmas S
  using (lookup-ty-wkᵗ; lookup-ty-wkʳ; lookup-ty-wkᵉ)
open import TypeInference.OpenSyntax.Subst          S

open import TypeInference.Raw.Syntax S
open import TypeInference.Generate   S
open import TypeInference.Constraints.Syntax S
open import TypeInference.Principality S using (C[_,_]; Γ₊; M₊)

open import TypeInference.SolverImpl.Core.Rigid S using (∨-true; dec-true; true-dec)
open import TypeInference.SolverImpl.Localise S using (Outerₑ; Outerᵣ; freeᵉ; freeʳ; anyᶠ)
open import TypeInference.SolverImpl.Invariants.Outer S
open import TypeInference.SolverImpl.Invariants.Expand S using (Ren; mkRen; renᵗ; renʳ; renᵉ; ren-⨟; ren-wkᵗ; ren-wkʳ; ren-wkᵉ; ren-id)
open import TypeInference.SolverImpl.Invariants S opEnum
  using (Shape; module Driver; Inv; GoodMove; inv-init)
open import TypeInference.SolverImpl.State S using (init; _⟶_)
open import TypeInference.SolverImpl.Solve S opEnum using (solve; Wit)
open import TypeInference.Outcome using (solved)

------------------------------------------------------------------------
-- Weakening

module _ {Θ₁ Θ} {P : Subst Θ₁ Θ} where

  tygood-wkᵗ : ∀ A → TyGoodᵛ P A → TyGoodᵛ (P ⨟ˢ wkˢᵗ) (wkᵗ-v A)
  tygood-wkᵗ A g = subst (TyGoodᵛ (P ⨟ˢ wkˢᵗ)) (wkˢᵗ-v A) (tygoodᵛ-⨟ {P = P} GV-wkᵗ A g)

  tygood-wkʳ : ∀ A → TyGoodᵛ P A → TyGoodᵛ (P ⨟ˢ wkˢʳ) (wkʳ-v A)
  tygood-wkʳ A g = subst (TyGoodᵛ (P ⨟ˢ wkˢʳ)) (wkˢʳ-v A) (tygoodᵛ-⨟ {P = P} GV-wkʳ A g)

  tygood-wkᵉ : ∀ A → TyGoodᵛ P A → TyGoodᵛ (P ⨟ˢ wkˢᵉ) (wkᵉ-v A)
  tygood-wkᵉ A g = subst (TyGoodᵛ (P ⨟ˢ wkˢᵉ)) (wkˢᵉ-v A) (tygoodᵛ-⨟ {P = P} GV-wkᵉ A g)

  good-wkᵗ : ∀ {t} → Goodₑ P t → Goodₑ (P ⨟ˢ wkˢᵗ) (wkᵗ-e t)
  good-wkᵗ {t} g = subst (Goodₑ (P ⨟ˢ wkˢᵗ)) (wkˢᵗ-e t) (goodₑ-⨟ {P = P} GV-wkᵗ g)

  good-wkʳ : ∀ {t} → Goodₑ P t → Goodₑ (P ⨟ˢ wkˢʳ) (wkʳ-e t)
  good-wkʳ {t} g = subst (Goodₑ (P ⨟ˢ wkˢʳ)) (wkˢʳ-e t) (goodₑ-⨟ {P = P} GV-wkʳ g)

  good-wkᵉ : ∀ {t} → Goodₑ P t → Goodₑ (P ⨟ˢ wkˢᵉ) (wkᵉ-e t)
  good-wkᵉ {t} g = subst (Goodₑ (P ⨟ˢ wkˢᵉ)) (wkˢᵉ-e t) (goodₑ-⨟ {P = P} GV-wkᵉ g)

-- The types of a context

record CtxGood {Θ₁ Θ n} (P : Subst Θ₁ Θ) (Γ : OCtx Θ n) : Set where
  constructor mkCtx
  field
    ctxg : ∀ i → TyGoodᵛ P (lookup-ty Γ i)

open CtxGood public

module _ {Θ₁ Θ} {P : Subst Θ₁ Θ} where

  ctx-∷ : ∀ {n} {Γ : OCtx Θ n} {A} → CtxGood P Γ → TyGoodᵛ P A → CtxGood P (Γ ∷ A)
  ctx-∷ c g = mkCtx λ { zero → g ; (suc i) → ctxg c i }

  ctx-⟨⟩ : ∀ {n} {Γ : OCtx Θ n} {ρ} → CtxGood P Γ → CtxGood P (Γ ⟨ ρ ⟩)
  ctx-⟨⟩ c = mkCtx (ctxg c)

  ctx-wkᵗ : ∀ {n} {Γ : OCtx Θ n} → CtxGood P Γ → CtxGood (P ⨟ˢ wkˢᵗ) (wkᵗ-ctx Γ)
  ctx-wkᵗ {Γ = Γ} c = mkCtx λ i →
    subst (TyGoodᵛ (P ⨟ˢ wkˢᵗ)) (sym (lookup-ty-wkᵗ Γ i)) (tygood-wkᵗ (lookup-ty Γ i) (ctxg c i))

  ctx-wkʳ : ∀ {n} {Γ : OCtx Θ n} → CtxGood P Γ → CtxGood (P ⨟ˢ wkˢʳ) (wkʳ-ctx Γ)
  ctx-wkʳ {Γ = Γ} c = mkCtx λ i →
    subst (TyGoodᵛ (P ⨟ˢ wkˢʳ)) (sym (lookup-ty-wkʳ Γ i)) (tygood-wkʳ (lookup-ty Γ i) (ctxg c i))

  ctx-wkᵉ : ∀ {n} {Γ : OCtx Θ n} → CtxGood P Γ → CtxGood (P ⨟ˢ wkˢᵉ) (wkᵉ-ctx Γ)
  ctx-wkᵉ {Γ = Γ} c = mkCtx λ i →
    subst (TyGoodᵛ (P ⨟ˢ wkˢᵉ)) (sym (lookup-ty-wkᵉ Γ i)) (tygood-wkᵉ (lookup-ty Γ i) (ctxg c i))

ctx-⊆ : ∀ {Θ₁ Θ₂ Θ n} {P : Subst Θ₁ Θ} {P' : Subst Θ₂ Θ} {Γ : OCtx Θ n}
      → P ⊆ᶠ P' → CtxGood P Γ → CtxGood P' Γ
ctx-⊆ {Γ = Γ} inc c = mkCtx λ i → tygoodᵛ-⊆ inc (lookup-ty Γ i) (ctxg c i)

-- Constants and ground types

good-const : ∀ {Θ₁ Θ} {P : Subst Θ₁ Θ} → (c : E) → Goodₑ P (econst c)
good-const c = outer (λ ())

goodʳ-const : ∀ {Θ₁ Θ} {P : Subst Θ₁ Θ} → (c : R) → Goodᵣ P (rconst c)
goodʳ-const c = outer ((λ ()) , (λ ()))

tygood-ground : ∀ {Θ₁ Θ} {P : Subst Θ₁ Θ} → (g : GType) → TyGoodᵛ P (⌜_⌝ᵍ {Θ} g)
tygood-ground (GType.Base b)     = tt
tygood-ground GType.Unit         = tt
tygood-ground GType.Bool         = tt
tygood-ground GType.Empty        = tt
tygood-ground (g GType.|×|ᵍ g')  = tygood-ground g , tygood-ground g'
tygood-ground (GType.[ c ]ᵍ g)   = goodʳ-const c , tygood-ground g

-- A clause's bound: the rigid is the image of its binder

new-free : ∀ {Θ₁ Θ} → (X : Subst Θ₁ Θ) → freeᵉ (newᵉ {Θ}) (X ↑ᵉ) ≡ true
new-free {Θ = Θ} X =
  ∨-right (anyᶠ (λ α → occᵉ-v (newᵉ {Θ}) (sTy (X ↑ᵉ) α))) _
    (∨-right (anyᶠ (λ i → occᵉ-r (newᵉ {Θ}) (sR (X ↑ᵉ) i))) _
      (anyᶠ-intro (λ i → occᵉ-e (newᵉ {Θ}) (sE (X ↑ᵉ) i)) zero refl))
  where
    open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-v; occᵉ-r; occᵉ-e)
    open import TypeInference.SolverImpl.Core.Rigid S using (∨-right)

bound-good : ∀ {Θ₁ Θ} → (X : Subst Θ₁ Θ) → (c : E) → Goodₑ (X ↑ᵉ) (econst c ·̂ₑ evar (newᵉ {Θ}))
bound-good {Θ = Θ} X c = outer o
  where
    open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-e)

    o : Outerₑ (X ↑ᵉ) (econst c ·̂ₑ evar (newᵉ {Θ}))
    o {k} r = subst (λ x → freeᵉ x (X ↑ᵉ) ≡ true) (sym (true-dec (k ≟ᶠ newᵉ {Θ}) r)) (new-free X)

------------------------------------------------------------------------
-- Annotations: read through a renaming landing among `π`'s unknowns

record Ann {Θ₀ Θ₁ Θ} (ι : Subst Θ₀ Θ) (π : Subst Θ₁ Θ) : Set where
  constructor mkAnn
  field
    ann-ren : Ren ι
    ann-⊆   : ι ⊆ᶠ π

open Ann public

-- Every expression is over the unknowns of the identity

id-outerₑ : ∀ {Ψ} → (u : EExp Ψ) → Outerₑ (idˢ {Ψ}) u
id-outerₑ {Ψ} u {k} r =
  ∨-right (anyᶠ (λ α → occᵉ-v k (sTy (idˢ {Ψ}) α))) _
    (∨-right (anyᶠ (λ i → occᵉ-r k (sR (idˢ {Ψ}) i))) _
      (anyᶠ-intro (λ i → occᵉ-e k (sE (idˢ {Ψ}) i)) k (dec-true (k ≟ᶠ k) refl)))
  where
    open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-v; occᵉ-r; occᵉ-e)
    open import TypeInference.SolverImpl.Core.Rigid S using (∨-right)

id-outerᵣ : ∀ {Ψ} → (u : RExp Ψ) → Outerᵣ (idˢ {Ψ}) u
id-outerᵣ {Ψ} u = (λ {k} r → e k) , (λ {k} r → rr k)
  where
    open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-v; occᵉ-r; occᵉ-e; occʳ-v; occʳ-r)
    open import TypeInference.SolverImpl.Core.Rigid S using (∨-right; ∨-left)

    e : ∀ k → freeᵉ k (idˢ {Ψ}) ≡ true
    e k = ∨-right (anyᶠ (λ α → occᵉ-v k (sTy (idˢ {Ψ}) α))) _
            (∨-right (anyᶠ (λ i → occᵉ-r k (sR (idˢ {Ψ}) i))) _
              (anyᶠ-intro (λ i → occᵉ-e k (sE (idˢ {Ψ}) i)) k (dec-true (k ≟ᶠ k) refl)))

    rr : ∀ k → freeʳ k (idˢ {Ψ}) ≡ true
    rr k = ∨-right (anyᶠ (λ α → occʳ-v k (sTy (idˢ {Ψ}) α))) _
             (anyᶠ-intro (λ i → occʳ-r k (sR (idˢ {Ψ}) i)) k (dec-true (k ≟ᶠ k) refl))

mutual
  id-goodᵛ : ∀ {Ψ} → (B : OVType Ψ) → TyGoodᵛ (idˢ {Ψ}) B
  id-goodᵛ (tvar α)  = tt
  id-goodᵛ (Base b)  = tt
  id-goodᵛ Unit      = tt
  id-goodᵛ Bool      = tt
  id-goodᵛ Empty     = tt
  id-goodᵛ (A |×| B) = id-goodᵛ A , id-goodᵛ B
  id-goodᵛ (A ⇒ C)   = id-goodᵛ A , id-goodᶜ C
  id-goodᵛ ([ ρ ] A) = outer {ρ = ρ} (id-outerᵣ ρ) , id-goodᵛ A

  id-goodᶜ : ∀ {Ψ} → (C : OCType Ψ) → TyGoodᶜ (idˢ {Ψ}) C
  id-goodᶜ (A ‼ ε) = id-goodᵛ A , outer {ε = ε} (id-outerₑ ε)


module _ {Θ₀ Θ₁ Θ} {ι : Subst Θ₀ Θ} {π : Subst Θ₁ Θ} (a : Ann ι π) where

  private
    ι-good : GV (idˢ ⨟ˢ ι) ι
    ι-good = GV-ren (renᵗ (ann-ren a)) (renʳ (ann-ren a)) (renᵉ (ann-ren a))

    to-π : (idˢ ⨟ˢ ι) ⊆ᶠ π
    to-π = ⊆ᶠ-trans (≐→⊆ᶠ (⨟-idˡ ι)) (ann-⊆ a)

  ann-goodₑ : (u : EExp Θ₀) → Goodₑ π (u [ ι ]ᵉ)
  ann-goodₑ u = goodₑ-⊆ to-π (goodₑ-⨟ {P = idˢ} ι-good {u} (outer (id-outerₑ u)))

  ann-goodᵣ : (u : RExp Θ₀) → Goodᵣ π (u [ ι ]ʳ)
  ann-goodᵣ u = goodᵣ-⊆ to-π (goodᵣ-⨟ {P = idˢ} ι-good {u} (outer (id-outerᵣ u)))

  ann-goodᵛ : (B : OVType Θ₀) → TyGoodᵛ π (B [ ι ]ᵛ)
  ann-goodᵛ B = tygoodᵛ-⊆ to-π (B [ ι ]ᵛ) (tygoodᵛ-⨟ {P = idˢ} ι-good B (id-goodᵛ B))

-- Under binders

module _ {Θ₀ Θ₁ Θ} {ι : Subst Θ₀ Θ} {π : Subst Θ₁ Θ} where

  ann-wkᵗ : Ann ι π → Ann (ι ⨟ˢ wkˢᵗ) (π ⨟ˢ wkˢᵗ)
  ann-wkᵗ a = mkAnn (ren-⨟ (ann-ren a) ren-wkᵗ)
                    (⊆ᶠ-⨟ (ann-⊆ a) wkˢᵗ (λ α → suc α , refl))

  ann-wkʳ : Ann ι π → Ann (ι ⨟ˢ wkˢʳ) (π ⨟ˢ wkˢʳ)
  ann-wkʳ a = mkAnn (ren-⨟ (ann-ren a) ren-wkʳ)
                    (⊆ᶠ-⨟ (ann-⊆ a) wkˢʳ (λ α → α , refl))

  ann-wkᵉ : Ann ι π → Ann (ι ⨟ˢ wkˢᵉ) (π ⨟ˢ wkˢᵉ)
  ann-wkᵉ a = mkAnn (ren-⨟ (ann-ren a) ren-wkᵉ)
                    (⊆ᶠ-⨟ (ann-⊆ a) wkˢᵉ (λ α → α , refl))

  ann-↑ᵉ : Ann ι π → Ann (ι ↑ᵉ) (π ↑ᵉ)
  ann-↑ᵉ a = mkAnn (mkRen t r e) (⊆ᶠ-↑ᵉ (ann-⊆ a))
    where
      t : ∀ α → Σ[ β ∈ TyVar (Θ +e) ] (sTy (ι ↑ᵉ) α ≡ tvar β)
      t α with sTy ι α | renᵗ (ann-ren a) α
      ... | .(tvar β) | β , refl = β , refl

      r : ∀ i → Σ[ j ∈ RVar (Θ +e) ] (sR (ι ↑ᵉ) i ≡ rvar j)
      r i with sR ι i | renʳ (ann-ren a) i
      ... | .(rvar j) | j , refl = j , refl

      e : ∀ i → Σ[ j ∈ EVar (Θ +e) ] (sE (ι ↑ᵉ) i ≡ evar j)
      e zero    = zero , refl
      e (suc i) with sE ι i | renᵉ (ann-ren a) i
      ... | .(evar j) | j , refl = suc j , refl

------------------------------------------------------------------------
-- Generation

private
  ctx-wkᵗ² : ∀ {Θ₁ Θ n} {P : Subst Θ₁ Θ} {Γ : OCtx Θ n} → CtxGood P Γ
           → CtxGood ((P ⨟ˢ wkˢᵗ) ⨟ˢ wkˢᵗ) (wkᵗ-ctx (wkᵗ-ctx Γ))
  ctx-wkᵗ² c = ctx-wkᵗ (ctx-wkᵗ c)

  ty-wkᵗ² : ∀ {Θ₁ Θ} {P : Subst Θ₁ Θ} → ∀ A → TyGoodᵛ P A
          → TyGoodᵛ ((P ⨟ˢ wkˢᵗ) ⨟ˢ wkˢᵗ) (wkᵗ-v (wkᵗ-v A))
  ty-wkᵗ² A g = tygood-wkᵗ (wkᵗ-v A) (tygood-wkᵗ A g)

mutual

  genVˢ-shape : ∀ {Θ₀ Θ₁ Θ n} {π : Subst Θ₁ Θ} {ι : Subst Θ₀ Θ} {Γ : OCtx Θ n}
              → Ann ι π → CtxGood π Γ → (V : RawV Θ₀ n) → {A : OVType Θ}
              → TyGoodᵛ π A → Shape π (genVˢ ι Γ V A)
  genVˢ-shape a c (var i)     gA = (ctxg c i , gA) , tt
  genVˢ-shape a c (const B k) gA = tt , gA
  genVˢ-shape a c ⋆           gA = tt , gA
  genVˢ-shape a c true        gA = tt , gA
  genVˢ-shape a c false       gA = tt , gA
  genVˢ-shape a c ⦉ V₁ , V₂ ⦊  {A} gA =
    ((tt , tt) , ty-wkᵗ² A gA) ,
    genVˢ-shape a' c' V₁ tt , genVˢ-shape a' c' V₂ tt
    where
      a' = ann-wkᵗ (ann-wkᵗ a)
      c' = ctx-wkᵗ² c
  genVˢ-shape a c (lam M) {A} gA =
    ((tt , tt , whole _) , tygood-wkᵉ (wkᵗ-v (wkᵗ-v A)) (ty-wkᵗ² A gA)) ,
    genCˢ-shape (ann-wkᵉ (ann-wkᵗ (ann-wkᵗ a))) (ctx-∷ (ctx-wkᵉ (ctx-wkᵗ² c)) tt) M (tt , whole _)
  genVˢ-shape a c (lam[ B ] M) {A} gA =
    ((ann-goodᵛ a' B , tt , whole _) , tygood-wkᵉ (wkᵗ-v A) (tygood-wkᵗ A gA)) ,
    genCˢ-shape a' (ctx-∷ (ctx-wkᵉ (ctx-wkᵗ c)) (ann-goodᵛ a' B)) M (tt , whole _)
    where
      a' = ann-wkᵉ (ann-wkᵗ a)
  genVˢ-shape a c (V ⦂ᵛ B) gA =
    genVˢ-shape a c V (ann-goodᵛ a B) , ann-goodᵛ a B , gA

  genCˢ-shape : ∀ {Θ₀ Θ₁ Θ n} {π : Subst Θ₁ Θ} {ι : Subst Θ₀ Θ} {Γ : OCtx Θ n}
              → Ann ι π → CtxGood π Γ → (M : RawC Θ₀ n) → {C : OCType Θ}
              → TyGoodᶜ π C → Shape π (genCˢ ι Γ M C)
  genCˢ-shape a c (return V) {A ‼ t} (gA , gt) = genVˢ-shape a c V gA , gt
  genCˢ-shape a c (M₁ ⨟ M₂) {A ‼ t} (gA , gt) =
    genCˢ-shape a' c' M₁ (tt , whole _) ,
    genCˢ-shape a' (ctx-∷ (ctx-⟨⟩ c') tt) M₂
                (tygood-wkᵉ (wkᵉ-v (wkᵗ-v A)) (tygood-wkᵉ (wkᵗ-v A) (tygood-wkᵗ A gA)) , whole _) ,
    good-wkᵉ (good-wkᵉ (good-wkᵗ gt))
    where
      a' = ann-wkᵉ (ann-wkᵉ (ann-wkᵗ a))
      c' = ctx-wkᵉ (ctx-wkᵉ (ctx-wkᵗ c))
  genCˢ-shape a c (V₁ · V₂) {A ‼ t} (gA , gt) =
    genVˢ-shape a' c' V₁ (tt , tt , whole _) ,
    genVˢ-shape a' c' V₂ tt ,
    (tt , tygood-wkᵉ (wkᵗ-v (wkᵗ-v A)) (ty-wkᵗ² A gA)) ,
    good-wkᵉ (good-wkᵗ (good-wkᵗ gt))
    where
      a' = ann-wkᵉ (ann-wkᵗ (ann-wkᵗ a))
      c' = ctx-wkᵉ (ctx-wkᵗ² c)
  genCˢ-shape a c (match V `in M) {A ‼ t} (gA , gt) =
    genVˢ-shape a' c' V (tt , tt) ,
    genCˢ-shape a' (ctx-∷ (ctx-∷ c' tt) tt) M (ty-wkᵗ² A gA , good-wkᵗ (good-wkᵗ gt))
    where
      a' = ann-wkᵗ (ann-wkᵗ a)
      c' = ctx-wkᵗ² c
  genCˢ-shape a c (absurd V) {A ‼ t} (gA , gt) = genVˢ-shape a c V tt
  genCˢ-shape a c (if V `then M₁ `else M₂) {A ‼ t} g =
    genVˢ-shape a c V tt , genCˢ-shape a c M₁ g , genCˢ-shape a c M₂ g
  genCˢ-shape a c (perform op V M) {A ‼ t} (gA , gt) =
    genVˢ-shape a' c' V (tygood-ground (param op)) ,
    genCˢ-shape a' (ctx-∷ (ctx-⟨⟩ c') (tygood-ground (arity op))) M
                (tygood-wkᵉ A gA , whole _) ,
    good-wkᵉ gt
    where
      a' = ann-wkᵉ a
      c' = ctx-wkᵉ c
  genCˢ-shape a c (delay τ M) {A ‼ t} (gA , gt) =
    genCˢ-shape (ann-wkᵉ a) (ctx-⟨⟩ (ctx-wkᵉ c)) M (tygood-wkᵉ A gA , whole _) ,
    good-wkᵉ gt
  genCˢ-shape {π = π} a c (handle M `with H `in N) {A ‼ t} (gA , gt) =
    genCˢ-shape a' c' M (tt , whole _) ,
    genCˢ-shape a' (ctx-∷ (ctx-⟨⟩ c') tt) N (tt , whole _) ,
    (tt , tygood-wkᵉ _ (tygood-wkᵉ _ (ty-wkᵗ² A gA))) ,
    good-wkᵉ (good-wkᵉ (good-wkᵗ (good-wkᵗ gt))) ,
    λ op → genCˢ-shape (ann-↑ᵉ a')
             (ctx-∷ (ctx-∷ (ctx-⟨⟩ (ctx-⊆ (wk-⊆ᶠ-↑ᵉ π₄) (ctx-wkᵉ c')))
                           (tygood-ground (param op)))
                    (goodʳ-const _ , tygood-ground (arity op) , tt , whole _))
             (H op) (tt , bound-good π₄ (op-grade op))
    where
      π₄ = (((π ⨟ˢ wkˢᵗ) ⨟ˢ wkˢᵗ) ⨟ˢ wkˢᵉ) ⨟ˢ wkˢᵉ
      a' = ann-wkᵉ (ann-wkᵉ (ann-wkᵗ (ann-wkᵗ a)))
      c' = ctx-wkᵉ (ctx-wkᵉ (ctx-wkᵗ² c))
  genCˢ-shape a c (unbox i N) {A ‼ t} (gA , gt) =
    (ctxg c' i , whole _ , tt) , whole _ , (tt , tt) ,
    genCˢ-shape a' (ctx-∷ c' tt) N (tygood-wkʳ _ (ty-wkᵗ² A gA) , good-wkʳ (good-wkᵗ (good-wkᵗ gt)))
    where
      a' = ann-wkʳ (ann-wkᵗ (ann-wkᵗ a))
      c' = ctx-wkʳ (ctx-wkᵗ² c)
  genCˢ-shape a c (box ρ V N) {A ‼ t} (gA , gt) =
    genVˢ-shape a' (ctx-⟨⟩ c') V tt ,
    genCˢ-shape a' (ctx-∷ c' (ann-goodᵣ a' ρ , tt)) N (tygood-wkᵗ A gA , good-wkᵗ gt)
    where
      a' = ann-wkᵗ a
      c' = ctx-wkᵗ c
  genCˢ-shape a c (M ⦂ᶜ (B ‼ u)) {A ‼ t} (gA , gt) =
    genCˢ-shape a c M (ann-goodᵛ a B , ann-goodₑ a u) , (ann-goodᵛ a B , gA) , gt

-- The constraint of a program, read against the identity: every unknown
-- of its scope is the program's own, and generation takes it from there

C-shape : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → Shape idˢ C[ Γ , M ]
C-shape Γ M =
  genCˢ-shape (mkAnn ren-id ⊆ᶠ-refl) (mkCtx (λ i → id-goodᵛ (lookup-ty (Γ₊ Γ) i))) (M₊ M)
              (tt , whole _)

-- So a program's solved state keeps I1′ and I5

open Driver

solved-inv : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
           → ∀ {s'} {m : init ⟶ s'} {w : Wit s' C[ Γ , M ]}
           → solve init C[ Γ , M ] ≡ solved (s' , m , w)
           → Inv idˢ s' × GoodMove idˢ m
solved-inv Γ M eq = solve-inv idˢ init C[ Γ , M ] inv-init (C-shape Γ M) eq
