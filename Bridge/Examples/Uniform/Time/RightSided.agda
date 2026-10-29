------------------------------------------------------------------
-- A uniform handler typing, and completeness on it             --
--                                                              --
-- At right-sided intervals: the program                        --
--                                                              --
--   handle return () with                                      --
--     handler {return x ↦ return ();                           --
--              op p k ↦ perform op p (λ a. k a)}               --
--                                                              --
-- whose clause performs the operation again and resumes with   --
-- its answer. Its declarative typing `D`, the clause family    --
-- `forwarding`, is uniform: every member is the instantiation  --
-- of one open clause typing at a rigid continuation grade      --
-- (`uniform`). Inference types the program (`M-verdict`), and  --
-- its principal scheme factors `D` (`M-principal`) and, at the --
-- factoring instance, types the program in `D`'s context below --
-- `D`'s type (`M-below`).                                      --
--                                                              --
-- The same for a comparison, `return (2 < 3)`, whose typing    --
-- runs the comparison first and returns its outcome (`D₂`).    --
------------------------------------------------------------------

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Unit using (tt)

open import Util.Equality

open import OpenCalculus.Syntax.Scopes using (∅ˢ; _+e)
open import OpenCalculus.Examples.Specs using (module Time-RightSided)

module Bridge.Examples.Uniform.Time.RightSided where

open Time-RightSided using (spec; hints; enum)

open import Grades.Examples.Time.RightSided using (right-sided-intervals)
open import ClosedCalculus.Examples.Typing.Time.RightSided using (opTime)
open import ClosedCalculus.Examples.Typing.Core right-sided-intervals opTime
  using (forwarding; uₑ; _·ₑ_)
open import Grades.Examples.Worked.Operations using (Op)

open import Language.Types                  spec using (CType; Unit; Natₑ; _‼_)
import Language.Types spec as Ty
import ClosedCalculus.Syntax.Contexts spec as LC
open import Language.Comparisons using (lt)
open import ClosedCalculus.Syntax.Contexts  spec using (Ctx; [])
open import ClosedCalculus.Syntax.Subtyping spec using (_<:ᶜ_)
import ClosedCalculus.Syntax.Terms   spec as L
import ClosedCalculus.Syntax.Erasure spec as CE

open import OpenCalculus.Syntax.Grades          spec
open import OpenCalculus.Syntax.Types           spec using (OVType)
open import OpenCalculus.Syntax.Contexts        spec using (OCtx; []; _∷_; _⟨_⟩; Hd; Tl-∷; Tl-⟨⟩)
open import OpenCalculus.Hypotheses             spec
open import OpenCalculus.Typing                 spec
open import OpenCalculus.Syntax.Raw             spec
open import OpenCalculus.Inference.SolverImpl   spec hints enum using (infer)
open import OpenCalculus.Inference.Principality spec using (PrincipalScheme; Inference; typed; untypable; stuck)
open import OpenCalculus.Examples.Variables

open import Bridge.Instantiation.Types          spec
open import Bridge.Instantiation.Judgements     spec
open import Bridge.Instantiation.Correspondence spec
open import Bridge.Instantiation.Embedding      spec
open import Bridge.Instantiation.Completeness   spec hints enum

------------------------------------------------------------------------
-- The program

clause : Op → RawC (∅ˢ +e) 2
clause op = perform op v₁ (unbox (var (fsuc fzero)) (v₀ · v₁))

M : RawC ∅ˢ 0
M = handle (return ⋆) `with handler (return ⋆) clause

------------------------------------------------------------------------
-- Its declarative typing, the clauses by `forwarding`

D : [] L.⊢C⦂ Unit ‼ (uₑ ·ₑ uₑ)
D = L.handle L.return L.⋆ `with forwarding `in (L.return L.⋆)

------------------------------------------------------------------------
-- The open clause, at the rigid continuation grade

ok₀ : ∀ {A : OVType (∅ˢ +e)} → VarOK (wkᵉ-H (∅ᴴ {∅ˢ})) A ûᵣ
ok₀ = ≾ᵘ-ok ⊩≾̂ᵣ-refl

clauseᵒ : (op : Op) → Clause [] Unit op
clauseᵒ op =
  perform op (var (Tl-∷ Hd) ok₀)
    (unbox (res-var {z = Tl-∷ (Tl-⟨⟩ Hd)}) (eqᵣ ≡̂ᵣ-identityˡ)
      (var Hd ok₀ · var (Tl-∷ Hd) ok₀))

-- `D` is uniform: its clauses are typed by `clauseᵒ`, and it erases to
-- the elaboration of `M`, each member of `forwarding` to that of the
-- raw clause at its continuation grade

uniform : UniformTyping [] ∅ᴰ M D
uniform = u-handle (u-return u-⋆) clauseᵒ (λ op → refl) (u-return u-⋆) , refl

annFree : AnnFreeᶜ M
annFree = tt , tt , (λ op → tt , tt , tt , tt)

secondClass : SecondClassᶜ M
secondClass = tt , tt , (λ op → tt , tt , tt , tt)

------------------------------------------------------------------------
-- Inference types it

-- The statements are made for any term whose verdict `typed?` reads as
-- typed, and applied at `M`: only `typed?` of its verdict is evaluated.

typed? : ∀ {Θ n} {Γ : OCtx Θ n} {N : RawC Θ n} → Inference Γ N → Bool
typed? (typed _) = true
typed? _         = false

pick : ∀ {Θ n} → (Γ : OCtx Θ n) → (N : RawC Θ n) → T (typed? (infer Γ N))
     → Σ[ p ∈ PrincipalScheme Γ N ] (infer Γ N ≡ typed p)
pick Γ N t with infer Γ N
... | typed p   = p , refl
... | untypable = ⊥-elim t
... | stuck     = ⊥-elim t

module _ {Θ n} (Γ : OCtx Θ n) (N : RawC Θ n) (t : T (typed? (infer Γ N))) where

  verdict : Σ[ p ∈ PrincipalScheme Γ N ] (infer Γ N ≡ typed p)
  verdict = pick Γ N t

  -- the scheme factors every uniform typing

  principal : AnnFreeᶜ N → NoHandlerTypeᶜᵗˣ Γ
            → (σ₀ : DInst Θ) → ∀ {C} → (D : ⟦ Γ ⟧ᶜᵗˣ σ₀ L.⊢C⦂ C)
            → UniformTyping Γ σ₀ N D → Principalᴰ (proj₁ verdict) σ₀ C
  principal = infer-principal Γ N (proj₂ verdict)

  -- and, at the factoring instance, types the term in the typing's
  -- context below its type

  below : SecondClassᶜ N → AnnFreeᶜ N → NoHandlerTypeᶜᵗˣ Γ
        → (σ₀ : DInst Θ) → ∀ {C} → (D : ⟦ Γ ⟧ᶜᵗˣ σ₀ L.⊢C⦂ C)
        → UniformTyping Γ σ₀ N D
        → Σ[ C' ∈ CType ] Σ[ D' ∈ ⟦ Γ ⟧ᶜᵗˣ σ₀ L.⊢C⦂ C' ]
            ((C' <:ᶜ C) × (CE.⌊ D' ⌋ᶜ ≡ CE.⌊ D ⌋ᶜ))
  below = infer-principal-typing Γ N (proj₂ verdict)

-- At `M`: inference types it, its scheme factors `D`, and at the
-- factoring instance it types the program in `D`'s context below `D`'s
-- type

M-verdict : Σ[ p ∈ PrincipalScheme [] M ] (infer [] M ≡ typed p)
M-verdict = verdict [] M tt

M-principal : Principalᴰ (proj₁ (verdict [] M tt)) ∅ᴰ (Unit ‼ (uₑ ·ₑ uₑ))
M-principal = principal [] M tt annFree tt ∅ᴰ D uniform

M-below : Σ[ C' ∈ CType ] Σ[ D' ∈ [] L.⊢C⦂ C' ]
            ((C' <:ᶜ (Unit ‼ (uₑ ·ₑ uₑ))) × (CE.⌊ D' ⌋ᶜ ≡ CE.⌊ D ⌋ᶜ))
M-below = below [] M tt secondClass annFree tt ∅ᴰ D uniform

------------------------------------------------------------------------
-- A comparison: its typing runs it before the `return`, which reads the
-- outcome

M₂ : RawC ∅ˢ 0
M₂ = return (cmp lt (numeral 2) (numeral 3))

D₂ : [] L.⊢C⦂ Ty.Bool ‼ (uₑ ·ₑ uₑ)
D₂ = L.cmp lt (L.numeralᵛ 2) (L.numeralᵛ 3) Natₑ L.⨟ L.return (L.var (λ ¬et → ⊥-elim (¬et Ty.Boolₑ)) LC.Hd)

uniform₂ : UniformTyping [] ∅ᴰ M₂ D₂
uniform₂ =
  u-hoist tt tt (u-succ (u-succ u-zero)) (u-succ (u-succ (u-succ u-zero)))
          (u-return (u-out (here refl))) ,
  refl

M₂-verdict : Σ[ p ∈ PrincipalScheme [] M₂ ] (infer [] M₂ ≡ typed p)
M₂-verdict = verdict [] M₂ tt

M₂-principal : Principalᴰ (proj₁ (verdict [] M₂ tt)) ∅ᴰ (Ty.Bool ‼ (uₑ ·ₑ uₑ))
M₂-principal = principal [] M₂ tt (tt , tt) tt ∅ᴰ D₂ uniform₂
