------------------------------------------------------------------------
-- Subsumption for contexts.                                          --
--                                                                    --
-- A computation over a binder of `A` is one over a binder of any     --
-- subtype of `A`: weaken, then substitute the subsumed variable.     --
-- The laws below meet it with a substitution, with a renaming of the --
-- rest of the context, and with a cast.                              --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.Syntax.Substitution.Subsumption (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming.Action S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Substitution    S
open import MonomorphicCalculus.Syntax.Types           S

open import MonomorphicCalculus.Syntax.Renaming.Equivalence  S
open import MonomorphicCalculus.Syntax.Renaming.Coherence    S
open import MonomorphicCalculus.Syntax.Terms.Equivalence     S
open import MonomorphicCalculus.Syntax.Terms.Transport       S

open import MonomorphicCalculus.Syntax.Substitution.Base    S
open import MonomorphicCalculus.Syntax.Substitution.Action  S
open import MonomorphicCalculus.Syntax.Substitution.Laws    S

-- Subsuming the top binder. The two sequencing congruences of the
-- operational semantics need it: a step refines the bound value's type,
-- while `_⨟_` and a handler's return clause, unlike `unbox`, carry no
-- witness of their own.

subCtx : ∀ {Γ A A₀ C} → A₀ <:ᵛ A → Γ ∷ A ⊢ᶜ⦂ C → Γ ∷ A₀ ⊢ᶜ⦂ C
subCtx p N =
  C-rename (cong-∷-ren wk-ren) N [ subV (var Hd (≾ᵘ-ok ≾ᵣ-refl)) p ]₀

-- Substituting into a subsumed binder subsumes the value first.

subCtx-sub : ∀ {Γ A A₀ C} → (w : A₀ <:ᵛ A) → (N : Γ ∷ A ⊢ᶜ⦂ C)
           → (V : Γ ⊢ᵛ⦂ A₀)
           ----------------------------------------------------------
           → subCtx w N [ V ]₀ ≡ N [ subV V w ]₀

subCtx-sub {A = A} w N V =
  trans (sub-swap-≡ᶜ V (subV (var Hd (≾ᵘ-ok ≾ᵣ-refl)) w)
                     (C-rename (cong-∷-ren wk-ren) N))
        (cong (C-sub₀ (val-sub (subV V w))) (sub-wk-≡ᶜ ([] ∷ A) V N))

-- Subsumption only touches the top binder, so a renaming of the rest passes
-- it.

subCtx-ren : ∀ {Γ Δ A A₀ C} → (r : Ren [] Δ Γ) → (w : A₀ <:ᵛ A)
           → (N : Γ ∷ A ⊢ᶜ⦂ C)
           ------------------------------------------------
           → C-rename (cong-∷-ren r) (subCtx w N)
           ≡ subCtx w (C-rename (cong-∷-ren r) N)

subCtx-ren r w N =
  trans (sym (ren-sub-≡ᶜ [] (cong-∷-ren r)
                         (subV (var Hd (≾ᵘ-ok ≾ᵣ-refl)) w)
                         (C-rename (cong-∷-ren wk-ren) N)))
        (cong₂ (λ U X → C-sub₀ (val-sub U) X) (subV-≡ refl) renM)
  where
    renM : C-rename (cong-∷-ren (cong-∷-ren r))
             (C-rename (cong-∷-ren wk-ren) N)
         ≡ C-rename (cong-∷-ren wk-ren) (C-rename (cong-∷-ren r) N)
    renM =
      trans (sym (C-rename-∘ (cong-∷-ren wk-ren)
                             (cong-∷-ren (cong-∷-ren r)) N))
        (trans
          (C-rename-≡
            (≐ʳ-trans (≐ʳ-sym (cong-∷-ren-∘-≐ʳ wk-ren (cong-∷-ren r)))
              (≐ʳ-trans (cong-∷-ren-≐ʳ (wk-ren-nat-≐ʳ r))
                        (cong-∷-ren-∘-≐ʳ r wk-ren)))
            N)
          (C-rename-∘ (cong-∷-ren r) (cong-∷-ren wk-ren) N))

-- Subsumption is stable under a context equality, the binder it subsumes
-- being the one the equality leaves alone.

subCtx-cast : ∀ {Γ Γ' A A₀ C} → (f : Ctx → Ctx) → (e : Γ' ≡ Γ)
            → (w : A₀ <:ᵛ A) → (N : f Γ' ∷ A ⊢ᶜ⦂ C)
            ----------------------------------------------------
            → subCtx w (castᶜ (cong (λ Γ₀ → f Γ₀ ∷ A) e) N)
            ≡ castᶜ (cong (λ Γ₀ → f Γ₀ ∷ A₀) e) (subCtx w N)

subCtx-cast f refl w N = refl
