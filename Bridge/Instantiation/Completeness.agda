------------------------------------------------------------------
-- Completeness of inference for the declarative system         --
--                                                              --
-- For uniform handlers and annotation-free terms. A uniform    --
-- declarative typing `D` of `M` at an instance `σ₀` of the     --
-- context's variables (`UniformTyping Γ σ₀ M D`) embeds in the --
-- open calculus at the empty scope                             --
-- (`Bridge.Instantiation.Embedding`) and so factors through a  --
-- principal scheme (`factor`): the factoring instance          --
-- satisfies the scheme's hypotheses and obligations, agrees    --
-- with `σ₀` on the context, and there the principal type is a  --
-- subtype of that of `D` (`principalᴰ`, `infer-principal`,     --
-- `check-principal`). An untypable verdict leaves no such      --
-- typing (`infer-untypableᴰ`, `check-untypableᴰ`). Soundness   --
-- is `Bridge.Instantiation.Inference`; the factoring instance  --
-- meets its premises (`principal-premises`), so the scheme     --
-- there types the term of `D`, which is `M` at `σ₀`            --
-- (`uniform-erasure`), in `D`'s context below `D`'s type       --
-- (`principal-typing`, `infer-principal-typing`).              --
------------------------------------------------------------------

open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.SolverImpl.Enum using (OpEnum)

module Bridge.Instantiation.Completeness (S : LanguageSpec) (opEnum : OpEnum S) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Language.Types                  S
open import ClosedCalculus.Syntax.Contexts  S using (Ctx)
open import ClosedCalculus.Syntax.Terms     S using (_⊢C⦂_)
open import ClosedCalculus.Syntax.Subtyping S using (_<:ᶜ_)

open import OpenCalculus.Syntax.Types         S using (OCType)
open import OpenCalculus.Syntax.Contexts      S using (OCtx)
open import OpenCalculus.Syntax.Subst         S
open import OpenCalculus.Hypotheses           S using (∅ᴴ; ⊩ᴴ-∅)
open import OpenCalculus.Hypotheses.Instances S
  using (Satisfiable; _⊩ᴼˢ_[_])
open import OpenCalculus.Typing     S using (_∣_⊢C⦂_)
open import OpenCalculus.Syntax.Raw S using (RawC)
import OpenCalculus.Typing.Erasure S as OE
open import OpenCalculus.Syntax.Raw.Subst       S
open import OpenCalculus.Inference.Principality S
  using (PrincipalScheme; module PrincipalScheme; Typable; typable;
         typed; established; untypable)
open import OpenCalculus.Inference.SolverImpl           S opEnum
  using (infer; check; infer-untypable; check-untypable)

open import Bridge.Instantiation.Types          S
open import Bridge.Instantiation.Judgements     S
open import Bridge.Instantiation.Correspondence S
open import Bridge.Instantiation.Terms          S using (⌊_⌋ᴿᶜ; ⌊≗⌋ᴿᶜ; ⌊[]⌋ᴿᶜ; castᶜ; castᶜ-⌊⌋)
open import Bridge.Instantiation.Embedding      S
open import Bridge.Instantiation.Inference      S opEnum using (scheme-instantiate)
import ClosedCalculus.Syntax.Erasure S as CE

open PrincipalScheme

-- `D` is a uniform typing of `M` in `Γ` at `σ₀`: in the open context
-- `Γ [ ⌜ σ₀ ⌝ˢ ]ᶜᵗˣ`, whose meaning is `⟦ Γ ⟧ᶜᵗˣ σ₀`, of the raw term
-- with its box grades at `σ₀`

UniformTyping : ∀ {Θ n} → (Γ : OCtx Θ n) → (σ₀ : DInst Θ) → RawC Θ n
              → ∀ {C} → ⟦ Γ ⟧ᶜᵗˣ σ₀ ⊢C⦂ C → Set
UniformTyping Γ σ₀ M D = Uᶜ (Γ [ ⌜ σ₀ ⌝ˢ ]ᶜᵗˣ) (M [ ⌜ σ₀ ⌝ˢ ]ᴿᶜ) D

module _ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} where

  -- the meaning of the instantiated context

  ⌞Γ⌜σ₀⌝⌟ : (σ₀ : DInst Θ) → ⌞ Γ [ ⌜ σ₀ ⌝ˢ ]ᶜᵗˣ ⌟ᶜᵗˣ ≡ ⟦ Γ ⟧ᶜᵗˣ σ₀
  ⌞Γ⌜σ₀⌝⌟ σ₀ = trans (⌞[]⌟ᶜᵗˣ ⌜ σ₀ ⌝ˢ Γ) (⟦≗⟧ᶜᵗˣ ⌞⌜ σ₀ ⌝ˢ⌟ Γ)

  -- a uniform typing of an annotation-free term is a typing in the
  -- open calculus, at the instance `⌜ σ₀ ⌝ˢ`

  embed-typing : AnnFreeᶜ M → (σ₀ : DInst Θ) → ∀ {C} → (D : ⟦ Γ ⟧ᶜᵗˣ σ₀ ⊢C⦂ C)
               → UniformTyping Γ σ₀ M D
               → Σ[ D' ∈ ∅ᴴ ∣ Γ [ ⌜ σ₀ ⌝ˢ ]ᶜᵗˣ ⊢C⦂ ⌜ C ⌝ᶜ ]
                   (OE.⌊ D' ⌋ᶜ ≡ M [ ⌜ σ₀ ⌝ˢ ]ᴿᶜ)
  embed-typing a σ₀ D u = embedᶜ u (annFree-[]ᶜ M ⌜ σ₀ ⌝ˢ a) (⌞Γ⌜σ₀⌝⌟ σ₀)

  -- a uniform typing is of the term at `σ₀`

  uniform-erasure : (σ₀ : DInst Θ) → ∀ {C} → (D : ⟦ Γ ⟧ᶜᵗˣ σ₀ ⊢C⦂ C)
                  → UniformTyping Γ σ₀ M D → CE.⌊ D ⌋ᶜ ≡ ⌊ M ⌋ᴿᶜ σ₀
  uniform-erasure σ₀ D u =
    trans (uniform-⌊⌋ᶜ u) (trans (⌊[]⌋ᴿᶜ M ⌜ σ₀ ⌝ˢ ∅ᴰ) (⌊≗⌋ᴿᶜ ⌞⌜ σ₀ ⌝ˢ⌟ M))

  -- so `M` is typable

  uniform-typable : AnnFreeᶜ M → (σ₀ : DInst Θ) → ∀ {C} → (D : ⟦ Γ ⟧ᶜᵗˣ σ₀ ⊢C⦂ C)
                  → UniformTyping Γ σ₀ M D → Typable Γ M
  uniform-typable a σ₀ {C} D u with embed-typing a σ₀ D u
  ... | D' , e = typable ∅ˢ ⌜ σ₀ ⌝ˢ ∅ᴴ ⌜ C ⌝ᶜ D' e (idˢ , ⊩ᴴ-∅ , []ᴬ)

-- The principal scheme's instance factoring a declarative typing: the
-- closed instance `δ` that `factor` yields from the embedded typing, read
-- declaratively as `⌞ δ ⌟ˢ`. It satisfies the hypotheses, and the
-- obligations in `factor`'s reading, the open entailment at `δ`, and so
-- pointwise; it agrees with `σ₀` on the context's variables; and there
-- the principal type is a subtype of the typing's.

record Principalᴰ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n}
                  (p : PrincipalScheme Γ M) (σ₀ : DInst Θ) (C : CType) : Set where
  field
    δ      : Subst (Θ̃ p) ∅ˢ
    sat-Q  : ⌞ δ ⌟ˢ ⊨ᴰ Q̃ p
    sat-R  : ∅ᴴ ⊩ᴼˢ R̃ p [ δ ]
    sat-Rᴰ : ⌞ δ ⌟ˢ ⊨ᴰᴿ R̃ p
    agree  : (σ̃ p ⨟ᴰ ⌞ δ ⌟ˢ) ≗ᴰ σ₀
    ctx    : ⟦ Γ [ σ̃ p ]ᶜᵗˣ ⟧ᶜᵗˣ ⌞ δ ⌟ˢ ≡ ⟦ Γ ⟧ᶜᵗˣ σ₀
    below  : ⟦ X̃ p ⟧ᶜ ⌞ δ ⌟ˢ <:ᶜ C

-- Declarative principality: a uniform typing of an annotation-free term
-- factors through every principal scheme

principalᴰ : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} → (p : PrincipalScheme Γ M)
           → AnnFreeᶜ M → (σ₀ : DInst Θ) → ∀ {C} → (D : ⟦ Γ ⟧ᶜᵗˣ σ₀ ⊢C⦂ C)
           → UniformTyping Γ σ₀ M D
           → Principalᴰ p σ₀ C
principalᴰ {Γ = Γ} {M} p a σ₀ {C} D u with embed-typing {Γ = Γ} {M} a σ₀ D u
... | D' , e with factor p ⌜ σ₀ ⌝ˢ ∅ᴴ D' e idˢ (⊩ᴴ-∅ , []ᴬ)
... | δ , tri , (hQ , hR) , le = record
  { δ      = δ
  ; sat-Q  = ⊨→⊨ᴰ (hQ , []ᴬ)
  ; sat-R  = hR
  ; sat-Rᴰ = ⊩ᴼˢ→⊨ᴰᴿ hR
  ; agree  = agree
  ; ctx    = trans (⟦[]⟧ᶜᵗˣ (σ̃ p) ⌞ δ ⌟ˢ Γ) (⟦≗⟧ᶜᵗˣ agree Γ)
  ; below  = subst₂ _<:ᶜ_ (⌞[]⌟ᶜ δ (X̃ p))
                    (trans (cong ⌞_⌟ᶜ ([id]ᶜ ⌜ C ⌝ᶜ)) ⌞⌜ C ⌝⌟ᶜ)
                    (sound-<:ᶜ (⊨ᴰ-∅ {σ = ∅ᴰ}) le)
  }
  where
    agree : (σ̃ p ⨟ᴰ ⌞ δ ⌟ˢ) ≗ᴰ σ₀
    agree = mk≗ᴰ
      (λ α → trans (sym (⟦[]⟧ᵛ δ ∅ᴰ (sTy (σ̃ p) α)))
               (trans (cong ⌞_⌟ᵛ (≐ᵗ tri α))
                 (trans (cong ⌞_⌟ᵛ ([id]ᵛ ⌜ ty σ₀ α ⌝ᵛ)) ⌞⌜ ty σ₀ α ⌝⌟ᵛ)))
      (λ i → trans (sym (⟦[]⟧ʳ δ ∅ᴰ (sR (σ̃ p) i))) (cong ⌞_⌟ʳ (≐ʳ tri i)))
      (λ i → trans (sym (⟦[]⟧ᵉ δ ∅ᴰ (sE (σ̃ p) i))) (cong ⌞_⌟ᵉ (≐ᵉ tri i)))

-- Inference: a typed verdict's scheme is principal for uniform typings

infer-principal : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → {p : PrincipalScheme Γ M}
                → infer Γ M ≡ typed p
                → AnnFreeᶜ M → (σ₀ : DInst Θ) → ∀ {C} → (D : ⟦ Γ ⟧ᶜᵗˣ σ₀ ⊢C⦂ C)
                → UniformTyping Γ σ₀ M D
                → Principalᴰ p σ₀ C
infer-principal Γ M {p} _ = principalᴰ p

-- and an untypable verdict leaves no uniform typing

infer-untypableᴰ : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                 → infer Γ M ≡ untypable → AnnFreeᶜ M
                 → ¬ (Σ[ σ₀ ∈ DInst Θ ] Σ[ C ∈ CType ] Σ[ D ∈ ⟦ Γ ⟧ᶜᵗˣ σ₀ ⊢C⦂ C ]
                        UniformTyping Γ σ₀ M D)
infer-untypableᴰ Γ M eq a (σ₀ , C , D , u) =
  infer-untypable Γ M eq (uniform-typable {Γ = Γ} {M} a σ₀ D u)

-- Checking: the same through an established check's scheme, and from an
-- untypable verdict

check-principal : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                → {p : PrincipalScheme Γ M} → {e : Satisfiable (Q̃ p) (R̃ p)}
                → check Γ M ≡ established p e
                → AnnFreeᶜ M → (σ₀ : DInst Θ) → ∀ {C} → (D : ⟦ Γ ⟧ᶜᵗˣ σ₀ ⊢C⦂ C)
                → UniformTyping Γ σ₀ M D
                → Principalᴰ p σ₀ C
check-principal Γ M {p} _ = principalᴰ p

check-untypableᴰ : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
                 → check Γ M ≡ untypable → AnnFreeᶜ M
                 → ¬ (Σ[ σ₀ ∈ DInst Θ ] Σ[ C ∈ CType ] Σ[ D ∈ ⟦ Γ ⟧ᶜᵗˣ σ₀ ⊢C⦂ C ]
                        UniformTyping Γ σ₀ M D)
check-untypableᴰ Γ M eq a (σ₀ , C , D , u) =
  check-untypable Γ M eq (uniform-typable {Γ = Γ} {M} a σ₀ D u)

------------------------------------------------------------------------
-- The round trip: the factoring instance of `principalᴰ`, read as
-- `⌞ δ ⌟ˢ`, meets the premises of the scheme's instantiation
-- (`Bridge.Instantiation.Inference`), its obligations through the
-- convertibility of `δ` and `⌜ ⌞ δ ⌟ˢ ⌝ˢ`

principal-premises : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} {p : PrincipalScheme Γ M}
                       {σ₀ : DInst Θ} {C : CType}
                   → (P : Principalᴰ p σ₀ C)
                   → (⌞ Principalᴰ.δ P ⌟ˢ ⊨ᴰ Q̃ p)
                   × (∅ᴴ ⊩ᴼˢ R̃ p [ ⌜ ⌞ Principalᴰ.δ P ⌟ˢ ⌝ˢ ])
principal-premises P = sat-Q , ⊩ᴼˢ-⌜⌞⌟⌝ δ sat-R
  where open Principalᴰ P

-- so the principal scheme, at that instance, types the term of a
-- uniform typing `D` in `D`'s context, at a subtype of `D`'s type

principal-typing : ∀ {Θ n} {Γ : OCtx Θ n} {M : RawC Θ n} → (p : PrincipalScheme Γ M)
                 → AnnFreeᶜ M → (σ₀ : DInst Θ) → ∀ {C} → (D : ⟦ Γ ⟧ᶜᵗˣ σ₀ ⊢C⦂ C)
                 → UniformTyping Γ σ₀ M D
                 → Σ[ C' ∈ CType ] Σ[ D' ∈ ⟦ Γ ⟧ᶜᵗˣ σ₀ ⊢C⦂ C' ]
                     ((C' <:ᶜ C) × (CE.⌊ D' ⌋ᶜ ≡ CE.⌊ D ⌋ᶜ))
principal-typing {Γ = Γ} {M} p a σ₀ D u
  with principalᴰ p a σ₀ D u
... | P with principal-premises P
...   | sQ , sR with scheme-instantiate p ⌞ Principalᴰ.δ P ⌟ˢ sQ sR
...     | D' , e =
  ⟦ X̃ p ⟧ᶜ ⌞ Principalᴰ.δ P ⌟ˢ ,
  castᶜ (Principalᴰ.ctx P) refl D' ,
  Principalᴰ.below P ,
  trans (castᶜ-⌊⌋ (Principalᴰ.ctx P) refl D')
        (trans e (trans (⌊≗⌋ᴿᶜ (Principalᴰ.agree P) M)
                        (sym (uniform-erasure {Γ = Γ} {M} σ₀ D u))))

infer-principal-typing : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → {p : PrincipalScheme Γ M}
                       → infer Γ M ≡ typed p
                       → AnnFreeᶜ M → (σ₀ : DInst Θ) → ∀ {C} → (D : ⟦ Γ ⟧ᶜᵗˣ σ₀ ⊢C⦂ C)
                       → UniformTyping Γ σ₀ M D
                       → Σ[ C' ∈ CType ] Σ[ D' ∈ ⟦ Γ ⟧ᶜᵗˣ σ₀ ⊢C⦂ C' ]
                           ((C' <:ᶜ C) × (CE.⌊ D' ⌋ᶜ ≡ CE.⌊ D ⌋ᶜ))
infer-principal-typing Γ M {p} _ = principal-typing p
