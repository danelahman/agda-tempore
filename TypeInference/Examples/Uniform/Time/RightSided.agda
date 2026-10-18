------------------------------------------------------------------
-- A uniform handler typing, and completeness on it             --
--                                                              --
-- At right-sided intervals: the program                        --
--                                                              --
--   handle return () with op p k ↦ perform op p (λ a. k a)     --
--                    in return ()                              --
--                                                              --
-- whose clause performs the operation again and resumes with   --
-- its answer. Its declarative typing `D`, the clause family    --
-- `forwarding`, is uniform: every member is the instantiation  --
-- of one open clause typing at a rigid continuation grade      --
-- (`uniform`). Inference types the program (`M-verdict`), and  --
-- its principal scheme factors `D` (`M-principal`) and, at the --
-- factoring instance, types the program in `D`'s context below --
-- `D`'s type (`M-below`).                                      --
------------------------------------------------------------------

open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)

open import Util.Equality

open import TypeInference.Scopes using (∅ˢ; _+e)
open import TypeInference.Examples.Specs using (module Time-RightSided)

module TypeInference.Examples.Uniform.Time.RightSided where

open Time-RightSided using (spec; enum)

open import Syntax.Grades.Example.Time.RightSided using (right-sided-intervals; right-sided-witnesses)
open import Syntax.Grades.Example.Worked.Typing.Time.RightSided using (opTime)
open import Syntax.Grades.Example.Worked.Typing.Core right-sided-intervals opTime right-sided-witnesses
  using (forwarding; uₑ; _·ₑ_)
open import Syntax.Grades.Example.Worked.Operations using (Op)

open import Syntax.Types    spec using (CType; Unit; _‼_)
open import Syntax.Contexts spec using (Ctx; [])
open import Syntax.Subtyping spec using (_<:ᶜ_)
import Syntax.Language spec as L
import Syntax.Erasure  spec as CE

open import TypeInference.OpenSyntax.Grades    spec
open import TypeInference.OpenSyntax.Types     spec using (OVType)
open import TypeInference.OpenSyntax.Contexts  spec using (OCtx; []; _∷_; _⟨_⟩; Hd; Tl-∷; Tl-⟨⟩)
open import TypeInference.OpenSyntax.Hyps      spec
open import TypeInference.OpenSyntax.Language  spec
open import TypeInference.Raw.Syntax           spec
open import TypeInference.SolverImpl           spec enum using (infer)
open import TypeInference.Principality         spec using (PrincipalScheme; Inference; typed; untypable; stuck)
open import TypeInference.Examples.Variables

open import Instantiation.Types          spec
open import Instantiation.Judgements     spec
open import Instantiation.Correspondence spec
open import Instantiation.Terms          spec using (instᶜ-⌊⌋)
open import Instantiation.Embedding      spec
open import Instantiation.Completeness   spec enum

------------------------------------------------------------------------
-- The program

clause : Op → RawC (∅ˢ +e) 2
clause op = perform op v₁ (unbox (fsuc fzero) (v₀ · v₁))

M : RawC ∅ˢ 0
M = handle (return ⋆) `with clause `in (return ⋆)

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
    (unbox (Tl-∷ (Tl-⟨⟩ Hd)) (eqᵣ ≡̂ᵣ-identityˡ) (<:̂ᵛ-refl _)
      (var Hd ok₀ · var (Tl-∷ Hd) ok₀))

-- `D` is uniform: each member of `forwarding` is, up to erasure, the
-- instantiation of `clauseᵒ` at its continuation grade

uniform : UniformTyping [] ∅ᴰ M D
uniform =
  u-handle (u-return u-⋆) clauseᵒ (λ op → refl)
    (λ op c → sym (instᶜ-⌊⌋ (∅ᴰ ,ᵉᴰ c) (⊨ᴰ-,ᵉ c ⊨ᴰ-∅) (clauseᵒ op)))
    (u-return u-⋆)

annFree : AnnFreeᶜ M
annFree = tt , (λ op → tt , tt , tt) , tt

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

  principal : AnnFreeᶜ N → (σ₀ : DInst Θ) → ∀ {C} → (D : ⟦ Γ ⟧ᶜᵗˣ σ₀ L.⊢C⦂ C)
            → UniformTyping Γ σ₀ N D → Principalᴰ (proj₁ verdict) σ₀ C
  principal = infer-principal Γ N (proj₂ verdict)

  -- and, at the factoring instance, types the term in the typing's
  -- context below its type

  below : AnnFreeᶜ N → (σ₀ : DInst Θ) → ∀ {C} → (D : ⟦ Γ ⟧ᶜᵗˣ σ₀ L.⊢C⦂ C)
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
M-principal = principal [] M tt annFree ∅ᴰ D uniform

M-below : Σ[ C' ∈ CType ] Σ[ D' ∈ [] L.⊢C⦂ C' ]
            ((C' <:ᶜ (Unit ‼ (uₑ ·ₑ uₑ))) × (CE.⌊ D' ⌋ᶜ ≡ CE.⌊ D ⌋ᶜ))
M-below = below [] M tt annFree ∅ᴰ D uniform
