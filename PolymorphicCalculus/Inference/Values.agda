------------------------------------------------------------------
-- Type inference for values in program contexts                --
--                                                              --
-- Inference for a closed raw value `V` in a program context    --
-- `Δ` is inference for `return V` (`inferᵛ`, `checkᵛ`). A      --
-- scheme is principal, `V` typable exactly when its hypotheses --
-- are satisfiable (`inferᵛ-typed`); `untypable` only for       --
-- untypable values (`inferᵛ-untypable`); `stuck` only with     --
-- handlers or a definition with quantified hypotheses          --
-- (`inferᵛ-noRigid`). Inference misses no typing under no      --
-- hypotheses (`completenessᵛ`).                                --
------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Bundles using (_⇔_; Equivalence)
open import Relation.Nullary using (¬_)

open import Language.Spec

open import Util.Equality

open import Grades.Hints using (SystemHints)
open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.SolverImpl.Enum using (OpEnum)

module PolymorphicCalculus.Inference.Values (S : LanguageSpec)
  (hints : SystemHints (LanguageSpec.Grades S)) (opEnum : OpEnum S) where

open import PolymorphicCalculus.Syntax.Types         S
open import PolymorphicCalculus.Syntax.Contexts      S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses           S
open import PolymorphicCalculus.Hypotheses.Instances S using (_⊨_; Satisfiable)
open import PolymorphicCalculus.Typing               S
open import PolymorphicCalculus.Typing.Erasure       S
open import PolymorphicCalculus.Syntax.Raw           S using (RawV; return; HandlerFreeᵛ)
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S
open import PolymorphicCalculus.Inference.Principality S
open import PolymorphicCalculus.Inference.Generate S using (NoRigidᵛ; handlerFree-noRigidᵛ)
open import PolymorphicCalculus.Inference.SolverImpl S hints opEnum
  using (infer; check; infer-untypable; infer-noRigid; check-untypable; check-noRigid)

------------------------------------------------------------------------
-- Outcomes

data Inferenceᵛ (Δ : PCtx) (V : RawV ∅ˢ 0) : Set where
  typed     : PrincipalSchemeᵛ Δ V → Inferenceᵛ Δ V
  untypable : Inferenceᵛ Δ V
  stuck     : Inferenceᵛ Δ V

data Checkᵛ (Δ : PCtx) (V : RawV ∅ˢ 0) : Set where
  established   : (p : PrincipalSchemeᵛ Δ V) → Satisfiable (PrincipalSchemeᵛ.Q̃ p) → Checkᵛ Δ V
  untypable     : Checkᵛ Δ V
  unestablished : PrincipalSchemeᵛ Δ V → Checkᵛ Δ V
  stuck         : Checkᵛ Δ V

private

  fromInference : ∀ {Δ V} → Inference {∅ˢ} {0} ⌜ Δ ⌝ᵖ (return V) → Inferenceᵛ Δ V
  fromInference (typed p) = typed (valueScheme p)
  fromInference untypable = untypable
  fromInference stuck     = stuck

  fromCheck : ∀ {Δ V} → Check {∅ˢ} {0} ⌜ Δ ⌝ᵖ (return V) → Checkᵛ Δ V
  fromCheck (established p s) = established (valueScheme p) s
  fromCheck untypable         = untypable
  fromCheck (unestablished p) = unestablished (valueScheme p)
  fromCheck stuck             = stuck

  fromInference-untypable : ∀ {Δ V} → (i : Inference ⌜ Δ ⌝ᵖ (return V))
                          → fromInference i ≡ untypable → i ≡ untypable
  fromInference-untypable untypable refl = refl

  fromInference-stuck : ∀ {Δ V} → (i : Inference ⌜ Δ ⌝ᵖ (return V))
                      → fromInference i ≡ stuck → i ≡ stuck
  fromInference-stuck stuck refl = refl

  fromCheck-untypable : ∀ {Δ V} → (c : Check ⌜ Δ ⌝ᵖ (return V))
                      → fromCheck c ≡ untypable → c ≡ untypable
  fromCheck-untypable untypable refl = refl

  fromCheck-stuck : ∀ {Δ V} → (c : Check ⌜ Δ ⌝ᵖ (return V))
                  → fromCheck c ≡ stuck → c ≡ stuck
  fromCheck-stuck stuck refl = refl

  noRigid-⌜⌝ : ∀ {Δ} {V : RawV ∅ˢ 0} → NoRigidᵛ Δ V → NoRigidᵛ (defs (⌜_⌝ᵖ {∅ˢ} Δ)) V
  noRigid-⌜⌝ {Δ} {V} = subst (λ Δ' → NoRigidᵛ Δ' V) (sym (defs-⌜⌝ Δ))

inferᵛ : (Δ : PCtx) → (V : RawV ∅ˢ 0) → Inferenceᵛ Δ V
inferᵛ Δ V = fromInference (infer ⌜ Δ ⌝ᵖ (return V))

checkᵛ : (Δ : PCtx) → (V : RawV ∅ˢ 0) → Checkᵛ Δ V
checkᵛ Δ V = fromCheck (check ⌜ Δ ⌝ᵖ (return V))

------------------------------------------------------------------------
-- Theorem (Type inference)

inferᵛ-typed : ∀ Δ V {p : PrincipalSchemeᵛ Δ V}
             → inferᵛ Δ V ≡ typed p → Typableᵛ Δ V ⇔ Satisfiable (PrincipalSchemeᵛ.Q̃ p)
inferᵛ-typed Δ V {p} _ = typableᵛ-⇔ p

inferᵛ-untypable : ∀ Δ V → inferᵛ Δ V ≡ untypable → ¬ Typableᵛ Δ V
inferᵛ-untypable Δ V e t =
  infer-untypable ⌜ Δ ⌝ᵖ (return V) (fromInference-untypable _ e) (typableᵛ→typable t)

inferᵛ-noRigid : ∀ Δ V → NoRigidᵛ Δ V → inferᵛ Δ V ≢ stuck
inferᵛ-noRigid Δ V h e =
  infer-noRigid ⌜ Δ ⌝ᵖ (return V) (noRigid-⌜⌝ {Δ} {V} h) (fromInference-stuck _ e)

inferᵛ-handlerFree : ∀ Δ V → Unquantified Δ → HandlerFreeᵛ V → inferᵛ Δ V ≢ stuck
inferᵛ-handlerFree Δ V u h = inferᵛ-noRigid Δ V (handlerFree-noRigidᵛ u V h)

checkᵛ-established : ∀ Δ V {p : PrincipalSchemeᵛ Δ V} {s}
                   → checkᵛ Δ V ≡ established p s → Typableᵛ Δ V
checkᵛ-established Δ V {p} {s} _ = Equivalence.from (typableᵛ-⇔ p) s

checkᵛ-untypable : ∀ Δ V → checkᵛ Δ V ≡ untypable → ¬ Typableᵛ Δ V
checkᵛ-untypable Δ V e t =
  check-untypable ⌜ Δ ⌝ᵖ (return V) (fromCheck-untypable _ e) (typableᵛ→typable t)

checkᵛ-noRigid : ∀ Δ V → NoRigidᵛ Δ V → checkᵛ Δ V ≢ stuck
checkᵛ-noRigid Δ V h e =
  check-noRigid ⌜ Δ ⌝ᵖ (return V) (noRigid-⌜⌝ {Δ} {V} h) (fromCheck-stuck _ e)

checkᵛ-handlerFree : ∀ Δ V → Unquantified Δ → HandlerFreeᵛ V → checkᵛ Δ V ≢ stuck
checkᵛ-handlerFree Δ V u h = checkᵛ-noRigid Δ V (handlerFree-noRigidᵛ u V h)

------------------------------------------------------------------------
-- Corollary (Completeness)

-- A typing of `V` in `Δ` over the empty scope from no hypotheses: no refutation,
-- and every scheme answered has a closed instance where its type is below the typing's

completenessᵛ : ∀ {Δ} {V : RawV ∅ˢ 0} {X : OVType ∅ˢ}
              → (D : ∅ᴴ ∣ ⌜ Δ ⌝ᵖ ⊢V⦂ X) → ⌊ D ⌋ᵛ ≡ V
              → (¬ inferᵛ Δ V ≡ untypable)
                × (∀ {p} → inferᵛ Δ V ≡ typed p
                   → Σ[ δ ∈ Subst (PrincipalSchemeᵛ.Θ̃ p) ∅ˢ ]
                       (δ ⊨ PrincipalSchemeᵛ.Q̃ p) × (∅ᴴ ∣ PrincipalSchemeᵛ.X̃ p [ δ ]ᵛ <:̂ᵛ X))
completenessᵛ {Δ} {V} {X} D e =
  (λ u → inferᵛ-untypable Δ V u (typableᵛ ∅ˢ ∅ᴴ X D e' (idˢ , ⊩ᴵ-∅))) ,
  λ {p} _ → scheme p
  where
    e' : ⌊ D ⌋ᵛ ≡ V [ from∅ ]ᴿᵛ
    e' = trans e (sym (trans ([≐]ᴿᵛ (from∅-≐ from∅ idˢ) V) ([id]ᴿᵛ V)))

    scheme : (p : PrincipalSchemeᵛ Δ V)
           → Σ[ δ ∈ Subst (PrincipalSchemeᵛ.Θ̃ p) ∅ˢ ]
               (δ ⊨ PrincipalSchemeᵛ.Q̃ p) × (∅ᴴ ∣ PrincipalSchemeᵛ.X̃ p [ δ ]ᵛ <:̂ᵛ X)
    scheme p with PrincipalSchemeᵛ.factor p ∅ᴴ D e' idˢ ⊩ᴵ-∅
    ... | δ , h , st = δ , h , subst (λ X' → ∅ᴴ ∣ _ <:̂ᵛ X') ([id]ᵛ X) st
