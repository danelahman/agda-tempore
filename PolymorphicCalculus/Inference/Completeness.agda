------------------------------------------------------------------
-- Completeness of constraint generation                        --
--                                                              --
-- A derivation erasing to an instance of a raw term satisfies, --
-- along that instance, the constraint generated from the term  --
-- (`completeV`, `completeC`). The expected type is an upper    --
-- bound: the derivation's type is a subtype of the             --
-- instantiated expected type, and its effect lies below the    --
-- instantiated expected effect. `charV` and `charC` combine    --
-- completeness with soundness into a characterisation of the   --
-- solutions.                                                   --
------------------------------------------------------------------

open import Data.Fin using (zero)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)

open import Function.Bundles using (_⇔_; mk⇔)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.Completeness (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades              S
open import PolymorphicCalculus.Syntax.Types               S
open import PolymorphicCalculus.Syntax.Contexts            S
open import PolymorphicCalculus.Syntax.Contexts.Properties S
open import PolymorphicCalculus.Syntax.GradeSubstitution   S
open import PolymorphicCalculus.Hypotheses                 S
open import PolymorphicCalculus.Typing                     S

open import PolymorphicCalculus.Syntax.Raw                   S
open import PolymorphicCalculus.Syntax.Raw.GradeSubstitution S
open import PolymorphicCalculus.Typing.Erasure               S

open import PolymorphicCalculus.Inference.Constraints.Syntax       S
open import PolymorphicCalculus.Inference.Constraints.Satisfaction S
open import PolymorphicCalculus.Inference.Constraints.Schemes      S using (instᶜ-complete)
open import PolymorphicCalculus.Inference.Constraints.Properties   S using (⊨-≐ᵥ)

open import PolymorphicCalculus.Inference.Generate  S
open import PolymorphicCalculus.Inference.Soundness S

-- The recursion is on the derivation; the raw term is read off by
-- inversion, `InvV`/`InvC`, which a subsumption passes on untouched.
-- Under a binder the inversion is re-established at the weakened
-- interpretation and the extended solution.

private

  reV : ∀ {Θ₀ Θ' n} {τ₁ τ : Subst Θ₀ Θ'} → τ₁ ≐ˢ τ → (V : RawV Θ₀ n)
      → {V' : RawV Θ' n} → V [ τ ]ᴿᵛ ≡ V' → InvV τ₁ V V'
  reV p V e = invV V (trans ([≐]ᴿᵛ p V) e)

  reC : ∀ {Θ₀ Θ' n} {τ₁ τ : Subst Θ₀ Θ'} → τ₁ ≐ˢ τ → (M : RawC Θ₀ n)
      → {M' : RawC Θ' n} → M [ τ ]ᴿᶜ ≡ M' → InvC τ₁ M M'
  reC p M e = invC M (trans ([≐]ᴿᶜ p M) e)

-- A use of a definition: its position is bound to the scheme of the
-- rule, and the instance of the rule solves the constraint

cmpUseDef : ∀ {Θ n Θ'} → (σ : Subst Θ Θ') → {Q : Hyps Θ'}
          → (Γ : OCtx Θ n) → (k : ℕ) → (A : OVType Θ) → (sc : Scheme)
          → sc ∈ᵖ[ k ] defs Γ → (δ : Subst (Θˢ sc) Θ') → Q ⊩ᴴ Qˢ sc [ δ ]
          → Q ∣ Xˢ sc [ δ ]ᵛ <:̂ᵛ A [ σ ]ᵛ
          → σ ⊨[ Q ] useDefConstraint (lookupᵖ (defs Γ) k) A
cmpUseDef σ Γ k A sc f δ h st rewrite ∈-lookupᵖ f = instᶜ-complete sc A δ st h

-- A resource value: the variable and the annotations of the raw value
-- are those of the judgement, which meets each annotation's atom

cmpR : ∀ {Θ₀ Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {Γ₀ : OCtx Θ' n}
         {ρ' ρ₀ ρ : RExp Θ'} {X₀ X : OVType Θ'} {z : [ ρ₀ ] X₀ ∈̂[ ρ' ] Γ₀}
     → (ι : Subst Θ₀ Θ) → (Γ : OCtx Θ n) → (V : RawV Θ₀ n)
     → (R : Q ∣ Γ₀ ⊢↪[ ρ' ] z ⦂[ ρ ] X)
     → InvV (ι ⨟ˢ σ) V ⌊ R ⌋ʳ
     → Γ₀ ≡ Γ [ σ ]ᶜᵗˣ
     ---------------------------------------------------------------------
     → (σ ⊨[ Q ] resC ι Γ V) × (resTy ι Γ V [ σ ]ᵛ ≡ [ ρ ] X) × (resGr Γ V [ σ ]ʳ ≡ ρ')
cmpR {σ = σ} {z = z} ι Γ _ res-var var ceq = tt , lty , lgr
  where
    i = var-pos z

    lty = trans (sym (lookup-ty-subst Γ σ i))
                (trans (cong (λ G → lookup-ty G i) (sym ceq)) (var-pos-ty z))

    lgr = trans (sym (lookup-gr-subst Γ σ i))
                (trans (cong (λ G → lookup-gr G i) (sym ceq)) (var-pos-gr z))
cmpR {σ = σ} {Q = Q} ι Γ _ (res-ann ρₐ Xₐ R p q) (annᵛ {V = V} {A = B} eV eB) ceq =
  (proj₁ c , subst₂ (Q ∣_<:̂ᵛ_) (sym (proj₁ (proj₂ c))) (sym eB') ([ p ]ₛ q)) ,
  eB' , proj₂ (proj₂ c)
  where
    c   = cmpR ι Γ V R (invV V eV) ceq
    eB' = trans ([⨟]ᵛ B ι σ) eB

mutual

  cmpV : ∀ {Θ₀ Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {Γ₀ : OCtx Θ' n}
       → (ι : Subst Θ₀ Θ) → (Γ : OCtx Θ n) → (A : OVType Θ) → (V : RawV Θ₀ n)
       → {A₀ : OVType Θ'}
       → (D : Q ∣ Γ₀ ⊢V⦂ A₀)
       → InvV (ι ⨟ˢ σ) V ⌊ D ⌋ᵛ
       → Γ₀ ≡ Γ [ σ ]ᶜᵗˣ
       → Q ∣ A₀ <:̂ᵛ A [ σ ]ᵛ
       --------------------------
       → σ ⊨[ Q ] genVˢ ι Γ V A

  -- variables
  --
  -- The raw index is `var-pos x`, at which the two lookups agree with the
  -- type and the grade of `x` itself.

  cmpV {σ = σ} {Q = Q} ι Γ A _ (var {A = A₁} {ρ = ρ₁} x ok) var ceq st =
    subst (λ z → Q ∣ z <:̂ᵛ A [ σ ]ᵛ) (sym lty) st , ok'
    where
      i = var-pos x

      lty : lookup-ty Γ i [ σ ]ᵛ ≡ A₁
      lty = trans (sym (lookup-ty-subst Γ σ i))
                  (trans (cong (λ G → lookup-ty G i) (sym ceq)) (var-pos-ty x))

      lgr : lookup-gr Γ i [ σ ]ʳ ≡ ρ₁
      lgr = trans (sym (lookup-gr-subst Γ σ i))
                  (trans (cong (λ G → lookup-gr G i) (sym ceq)) (var-pos-gr x))

      ok' : VarOK Q (lookup-ty Γ i [ σ ]ᵛ) (lookup-gr Γ i [ σ ]ʳ)
      ok' = subst₂ (VarOK Q) (sym lty) (sym lgr) ok

  -- uses of top-level definitions

  cmpV {σ = σ} ι Γ A _ (usedef {k = k} {s = sc} f δ h refl) usedef ceq st =
    cmpUseDef σ Γ k A sc (subst (sc ∈ᵖ[ k ]_) (trans (cong defs ceq) (defs-subst Γ σ)) f) δ h st

  -- base-typed constants, unit, booleans
  --
  -- None has a proper supertype, so the pin is recovered by inversion.

  cmpV {σ = σ} ι Γ A _ (const B c) const ceq st = ⊨-≐ᵥ σ (Base B) A (sym (<:̂ᵛ-Baseˡ st))
  cmpV {σ = σ} ι Γ A _ ⋆           ⋆     ceq st = ⊨-≐ᵥ σ Unit A (sym (<:̂ᵛ-Unitˡ st))
  cmpV {σ = σ} ι Γ A _ true        true  ceq st = ⊨-≐ᵥ σ Bool A (sym (<:̂ᵛ-Boolˡ st))
  cmpV {σ = σ} ι Γ A _ false       false ceq st = ⊨-≐ᵥ σ Bool A (sym (<:̂ᵛ-Boolˡ st))

  -- natural numbers

  cmpV {σ = σ} ι Γ A _ zero        zero  ceq st = ⊨-≐ᵥ σ Nat A (sym (<:̂ᵛ-Natˡ st))
  cmpV {σ = σ} ι Γ A _ (succ D) (succ {V = V} e) ceq st =
    ⊨-≐ᵥ σ Nat A (sym (<:̂ᵛ-Natˡ st)) , cmpV ι Γ Nat V D (invV V e) ceq Natₛ

  -- pairing
  --
  -- A supertype of a product is a product, so the slack splits between
  -- the two components.

  cmpV {Θ = Θ} {σ = σ} ι Γ A _ (⦉_,_⦊ {A = A₁} {B = A₂} D₁ D₂)
       (⦉_,_⦊ {V = V₁} {W = V₂} e₁ e₂) ceq st
    with <:̂ᵛ-×ˡ st
  ... | B₁ , B₂ , eq , st₁ , st₂ =
    B₁ , B₂ , ⊨-≐ᵥ (σ ,ᵗ B₁ ,ᵗ B₂) (α₁ |×| α₂) (wkᵗ-v (wkᵗ-v A)) (trans (sym eq) (sym pA)) ,
    ih₁ , ih₂
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})

      pΓ = co²ᵗ-ctx σ B₁ B₂ Γ
      pA = co²ᵗ-v   σ B₁ B₂ A
      pι = co²ᵗ-ˢ   ι σ B₁ B₂

      ih₁ = cmpV ι↑ Γ↑ α₁ V₁ D₁ (reV pι V₁ e₁) (trans ceq (sym pΓ)) st₁
      ih₂ = cmpV ι↑ Γ↑ α₂ V₂ D₂ (reV pι V₂ e₂) (trans ceq (sym pΓ)) st₂

  -- injections into a sum
  --
  -- A supertype of a sum is a sum; the injected summand carries its
  -- slack, the other is the supertype's own.

  cmpV {Θ = Θ} {σ = σ} ι Γ A _ (inl D₁) (inl {V = V} e) ceq st
    with <:̂ᵛ-+ˡ st
  ... | B₁ , B₂ , eq , st₁ , _ =
    B₁ , B₂ , ⊨-≐ᵥ (σ ,ᵗ B₁ ,ᵗ B₂) (α₁ |+| α₂) (wkᵗ-v (wkᵗ-v A)) (trans (sym eq) (sym pA)) ,
    cmpV ι↑ Γ↑ α₁ V D₁ (reV pι V e) (trans ceq (sym pΓ)) st₁
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})

      pΓ = co²ᵗ-ctx σ B₁ B₂ Γ
      pA = co²ᵗ-v   σ B₁ B₂ A
      pι = co²ᵗ-ˢ   ι σ B₁ B₂

  cmpV {Θ = Θ} {σ = σ} ι Γ A _ (inr D₂) (inr {V = V} e) ceq st
    with <:̂ᵛ-+ˡ st
  ... | B₁ , B₂ , eq , _ , st₂ =
    B₁ , B₂ , ⊨-≐ᵥ (σ ,ᵗ B₁ ,ᵗ B₂) (α₁ |+| α₂) (wkᵗ-v (wkᵗ-v A)) (trans (sym eq) (sym pA)) ,
    cmpV ι↑ Γ↑ α₂ V D₂ (reV pι V e) (trans ceq (sym pΓ)) st₂
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})

      pΓ = co²ᵗ-ctx σ B₁ B₂ Γ
      pA = co²ᵗ-v   σ B₁ B₂ A
      pι = co²ᵗ-ˢ   ι σ B₁ B₂

  -- lists
  --
  -- A supertype of a list type is a list type; its element type is the
  -- witness, the head carrying the slack and the tail its lifting.

  cmpV {Θ = Θ} {σ = σ} ι Γ A _ nil nil ceq st
    with <:̂ᵛ-Listˡ st
  ... | B , eq , _ =
    B , ⊨-≐ᵥ (σ ,ᵗ B) (|List| (tvar (newᵗ {Θ}))) (wkᵗ-v A) (trans (sym eq) (sym (wk-,ᵗ-v σ B A)))

  cmpV {Θ = Θ} {σ = σ} ι Γ A _ (cons D₁ D₂) (cons {V = V} {W = W} e₁ e₂) ceq st
    with <:̂ᵛ-Listˡ st
  ... | B , eq , st₁ =
    B , ⊨-≐ᵥ (σ ,ᵗ B) (|List| α) (wkᵗ-v A) (trans (sym eq) (sym pA)) ,
    cmpV ι↑ Γ↑ α V D₁ (reV pι V e₁) (trans ceq (sym pΓ)) st₁ ,
    cmpV ι↑ Γ↑ (|List| α) W D₂ (reV pι W e₂) (trans ceq (sym pΓ)) (|List|ₛ st₁)
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx Γ
      α  = tvar (newᵗ {Θ})

      pΓ = wk-,ᵗ-ctx σ B Γ
      pA = wk-,ᵗ-v   σ B A
      pι = wk-,ᵗ-ˢ   ι σ B

  -- comparison
  --
  -- The operands' type is its own witness; the result is pinned as for
  -- the boolean constants.

  cmpV {Θ = Θ} {σ = σ} {Q = Q} ι Γ A _
       (cmp {A = A₁} ⋈ D₁ D₂ et) (cmp {V = V} {W = W} e₁ e₂) ceq st =
    A₁ , ⊨-≐ᵥ (σ ,ᵗ A₁) Bool (wkᵗ-v A) (trans (sym (<:̂ᵛ-Boolˡ st)) (sym pA)) ,
    ih₁ , ih₂ , et
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx Γ
      α  = tvar (newᵗ {Θ})

      pΓ = wk-,ᵗ-ctx σ A₁ Γ
      pA = wk-,ᵗ-v   σ A₁ A
      pι = wk-,ᵗ-ˢ   ι σ A₁

      ih₁ = cmpV ι↑ Γ↑ α V D₁ (reV pι V e₁) (trans ceq (sym pΓ)) (<:̂ᵛ-refl _)
      ih₂ = cmpV ι↑ Γ↑ α W D₂ (reV pι W e₂) (trans ceq (sym pΓ)) (<:̂ᵛ-refl _)

  -- lambda abstraction

  cmpV {Θ = Θ} {σ = σ} {Q = Q} ι Γ A _
       (lam {A = A₁} {C = A₂ ‼ ε₀} D) (lam {M = M} e) ceq st =
    A₁ , A₂ , ε₀ , subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st , ih
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))
      α₁ = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      α₂ = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e₀ = evar (newᵉ {Θ +ty +ty})

      pΓ = co²ᵗᵉ-ctx σ A₁ A₂ ε₀ Γ
      pA = co²ᵗᵉ-v   σ A₁ A₂ ε₀ A
      pι = co²ᵗᵉ-ˢ   ι σ A₁ A₂ ε₀

      ih = cmpC ι↑ (Γ↑ ∷ α₁) α₂ e₀ M D (reC pι M e)
                (cong (_∷ A₁) (trans ceq (sym pΓ))) (<:̂ᵛ-refl _) ⊩≾̂ₑ-refl

  -- handlers
  --
  -- The clause family is handled pointwise; only the clause context's
  -- weakenings and the two ground-type embeddings need collapsing. The
  -- handler's result type is its own witness, so clauses and return
  -- clause are both typed at it and the slack sits in the one subtyping
  -- atom.

  cmpV {Θ = Θ} {Θ' = Θ'} {σ = σ} {Q = Q} ι Γ A _
       (handler {A = A₁} {B = A₂} {ε = ε₁} {ε' = ε₂} D₂ H)
       (handler {N = N} {H = R} eN eR) ceq st =
    A₁ , A₂ , ε₁ , ε₂ , subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st , ih₂ , ihH
    where
      ι↑  = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ
      σ'  = σ ,ᵗ A₁ ,ᵗ A₂ ,ᵉ ε₁ ,ᵉ ε₂
      Γ↑  = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ)))
      α   = wkᵉ-v (wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ}))))
      γ   = wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ +ty})))
      e₁  = wkᵉ-e (evar (newᵉ {Θ +ty +ty}))
      e₂  = evar (newᵉ {Θ +ty +ty +e})
      Γ⇑  = wkᵉ-ctx (wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))))
      γ⇑  = wkᵉ-v (wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ +ty}))))
      e'' = evar (newᵉ {Θ +ty +ty +e +e})

      pΓ  = co²ᵗ²ᵉ-ctx  σ A₁ A₂ ε₁ ε₂ Γ
      pA  = co²ᵗ²ᵉ-v    σ A₁ A₂ ε₁ ε₂ A
      pΓ⇑ = co²ᵗ²ᵉ-ctx↑ σ A₁ A₂ ε₁ ε₂ Γ
      pγ⇑ = wk-↑ᵉ-v σ' γ
      pι  = co²ᵗ²ᵉ-ˢ    ι σ A₁ A₂ ε₁ ε₂
      pι⇑ = co²ᵗ²ᵉ-ˢ↑   ι σ A₁ A₂ ε₁ ε₂

      ih₂ = cmpC ι↑ (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) γ e₂ N D₂ (reC pι N eN)
                 (cong (λ G → G ⟨ ∣ ε₁ ∣̂ᵉ ⟩ ∷ A₁) (trans ceq (sym pΓ)))
                 (<:̂ᵛ-refl _) ⊩≾̂ₑ-refl

      cH : (op : Op)
         → wkᵉ-ctx _ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
              ∷ [ rconst (mapᵉ (op-grade op)) ]
                  (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v _ ‼ evar (newᵉ {Θ'}))
           ≡ (Γ⇑ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                ∷ [ rconst (mapᵉ (op-grade op)) ] (⌜ arity op ⌝ᵍ ⇒ γ⇑ ‼ e''))
             [ σ' ↑ᵉ ]ᶜᵗˣ
      cH op =
        cong₂ _∷_
              (cong₂ _∷_ (cong (_⟨ rconst ⊤ᵣ ⟩) (trans (cong wkᵉ-ctx ceq) (sym pΓ⇑)))
                         (sym (⌜⌝ᵍ-subst (σ' ↑ᵉ) (param op))))
              (cong₂ (λ X Y → [ rconst (mapᵉ (op-grade op)) ]
                                (X ⇒ Y ‼ evar (newᵉ {Θ'})))
                     (sym (⌜⌝ᵍ-subst (σ' ↑ᵉ) (arity op)))
                     (sym pγ⇑))

      ihH : (op : Op) → _
      ihH op =
        cmpC (ι↑ ↑ᵉ)
             (Γ⇑ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                 ∷ [ rconst (mapᵉ (op-grade op)) ] (⌜ arity op ⌝ᵍ ⇒ γ⇑ ‼ e''))
             γ⇑ (econst (op-grade op) ·̂ₑ e'')
             (R op) (H op) (reC pι⇑ (R op) (eR op)) (cH op)
             (subst (λ z → wkᵉ-H Q ∣ wkᵉ-v A₂ <:̂ᵛ z) (sym pγ⇑)
                    (<:̂ᵛ-refl (wkᵉ-v A₂)))
             ⊩≾̂ₑ-refl

  -- type annotation
  --
  -- The recorded annotation is the instance of the raw one: the body is
  -- checked against it, and the slack sits in the subtyping atom.

  cmpV {σ = σ} {Q = Q} ι Γ A _ (annᵛ A₁ D) (annᵛ {V = V} {A = B} eV eB) ceq st =
    cmpV ι Γ (B [ ι ]ᵛ) V D (invV V eV) ceq
         (subst (λ z → Q ∣ A₁ <:̂ᵛ z) (sym pB) (<:̂ᵛ-refl A₁)) ,
    subst (λ z → Q ∣ z <:̂ᵛ A [ σ ]ᵛ) (sym pB) st
    where
      pB : B [ ι ]ᵛ [ σ ]ᵛ ≡ A₁
      pB = trans ([⨟]ᵛ B ι σ) eB

  -- subsumption
  --
  -- Invisible to erasure; its witness composes with the slack.

  cmpV ι Γ A V (subV D p) inv ceq st = cmpV ι Γ A V D inv ceq (<:̂ᵛ-trans p st)


  cmpC : ∀ {Θ₀ Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {Γ₀ : OCtx Θ' n}
       → (ι : Subst Θ₀ Θ) → (Γ : OCtx Θ n) → (A : OVType Θ) → (t : EExp Θ)
       → (M : RawC Θ₀ n)
       → {A₀ : OVType Θ'} → {ε₀ : EExp Θ'}
       → (D : Q ∣ Γ₀ ⊢C⦂ A₀ ‼ ε₀)
       → InvC (ι ⨟ˢ σ) M ⌊ D ⌋ᶜ
       → Γ₀ ≡ Γ [ σ ]ᶜᵗˣ
       → Q ∣ A₀ <:̂ᵛ A [ σ ]ᵛ
       → Q ⊩ ε₀ ≾̂ₑ t [ σ ]ᵉ
       --------------------------------
       → σ ⊨[ Q ] genCˢ ι Γ M (A ‼ t)

  -- returning a value

  cmpC ι Γ A t _ (return D) (return {V = V} e) ceq st le =
    cmpV ι Γ A V D (invV V e) ceq st , le

  -- sequential composition
  --
  -- The witnesses make the continuation's context an instance of the
  -- generated one on the nose: `∣ e₁ ∣̂ᵉ` instantiates to `∣ ε₁ ∣̂ᵉ`.

  cmpC {Θ = Θ} {σ = σ} {Q = Q} ι Γ A t _
       (_⨟_ {A = A₁} {ε' = ε₂} {ε = ε₁} D₁ D₂) (_⨟_ {M = M₁} {N = M₂} e₁' e₂') ceq st le =
    A₁ , ε₁ , ε₂ , ih₁ , ih₂ , subst (λ z → Q ⊩ ε₁ ·̂ₑ ε₂ ≾̂ₑ z) (sym pt) le
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ
      Γ↑ = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx Γ))
      A↑ = wkᵉ-v (wkᵉ-v (wkᵗ-v A))
      α  = wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ})))
      e₁ = wkᵉ-e (evar (newᵉ {Θ +ty}))
      e₂ = evar (newᵉ {Θ +ty +e})

      pΓ = coᵗ²ᵉ-ctx σ A₁ ε₁ ε₂ Γ
      pA = coᵗ²ᵉ-v   σ A₁ ε₁ ε₂ A
      pt = coᵗ²ᵉ-e   σ A₁ ε₁ ε₂ t
      pι = coᵗ²ᵉ-ˢ   ι σ A₁ ε₁ ε₂

      ih₁ = cmpC ι↑ Γ↑ α e₁ M₁ D₁ (reC pι M₁ e₁') (trans ceq (sym pΓ))
                 (<:̂ᵛ-refl _) ⊩≾̂ₑ-refl
      ih₂ = cmpC ι↑ (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) A↑ e₂ M₂ D₂ (reC pι M₂ e₂')
                 (cong (λ G → G ⟨ ∣ ε₁ ∣̂ᵉ ⟩ ∷ A₁) (trans ceq (sym pΓ)))
                 (subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st) ⊩≾̂ₑ-refl

  -- function application

  cmpC {Θ = Θ} {σ = σ} {Q = Q} ι Γ A t _
       (_·_ {A = A₁} {C = A₂ ‼ ε₀} D₁ D₂) (_·_ {V = V₁} {W = V₂} e₁ e₂) ceq st le =
    A₁ , A₂ , ε₀ , ih₁ , ih₂ ,
    subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st ,
    subst (λ z → Q ⊩ ε₀ ≾̂ₑ z) (sym pt) le
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))
      α  = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      β  = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})

      pΓ = co²ᵗᵉ-ctx σ A₁ A₂ ε₀ Γ
      pA = co²ᵗᵉ-v   σ A₁ A₂ ε₀ A
      pt = co²ᵗᵉ-e   σ A₁ A₂ ε₀ t
      pι = co²ᵗᵉ-ˢ   ι σ A₁ A₂ ε₀

      ih₁ = cmpV ι↑ Γ↑ (α ⇒ (β ‼ e)) V₁ D₁ (reV pι V₁ e₁) (trans ceq (sym pΓ))
                 (<:̂ᵛ-refl _)
      ih₂ = cmpV ι↑ Γ↑ α V₂ D₂ (reV pι V₂ e₂) (trans ceq (sym pΓ)) (<:̂ᵛ-refl _)

  -- pattern-matching

  cmpC {Θ = Θ} {σ = σ} {Q = Q} ι Γ A t _
       (match_`in_ {A = A₁} {B = A₂} D₁ D₂) (match {V = V} {M = M} e₁ e₂) ceq st le =
    A₁ , A₂ , ih₁ , ih₂
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)
      A↑ = wkᵗ-v (wkᵗ-v A)
      t↑ = wkᵗ-e (wkᵗ-e t)
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})

      pΓ = co²ᵗ-ctx σ A₁ A₂ Γ
      pA = co²ᵗ-v   σ A₁ A₂ A
      pt = co²ᵗ-e   σ A₁ A₂ t
      pι = co²ᵗ-ˢ   ι σ A₁ A₂

      ih₁ = cmpV ι↑ Γ↑ (α₁ |×| α₂) V D₁ (reV pι V e₁) (trans ceq (sym pΓ))
                 (<:̂ᵛ-refl _)
      ih₂ = cmpC ι↑ (Γ↑ ∷ α₁ ∷ α₂) A↑ t↑ M D₂ (reC pι M e₂)
                 (cong (λ G → G ∷ A₁ ∷ A₂) (trans ceq (sym pΓ)))
                 (subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st)
                 (subst (λ z → Q ⊩ _ ≾̂ₑ z) (sym pt) le)

  -- empty type elimination

  cmpC ι Γ A t _ (absurd D) (absurd {V = V} e) ceq st le =
    cmpV ι Γ Empty V D (invV V e) ceq Emptyₛ

  -- boolean elimination

  cmpC ι Γ A t _ (if_`then_`else_ D₀ D₁ D₂) (if {V = V} {M = M₁} {N = M₂} e₀ e₁ e₂)
       ceq st le =
    cmpV ι Γ Bool V D₀ (invV V e₀) ceq Boolₛ ,
    cmpC ι Γ A t M₁ D₁ (invC M₁ e₁) ceq st le ,
    cmpC ι Γ A t M₂ D₂ (invC M₂ e₂) ceq st le

  -- natural-number elimination

  cmpC ι Γ A t _ (caseℕ_`zero_`succ_ D₀ D₁ D₂)
       (caseℕ {V = V} {M = M₁} {N = M₂} e₀ e₁ e₂) ceq st le =
    cmpV ι Γ Nat V D₀ (invV V e₀) ceq Natₛ ,
    cmpC ι Γ A t M₁ D₁ (invC M₁ e₁) ceq st le ,
    cmpC ι (Γ ∷ Nat) A t M₂ D₂ (invC M₂ e₂) (cong (_∷ Nat) ceq) st le

  -- sum elimination
  --
  -- The summands are the scrutinee's own; the branches inherit the slack.

  cmpC {Θ = Θ} {σ = σ} {Q = Q} ι Γ A t _
       (case+_`inl_`inr_ {A = A₁} {B = A₂} D₀ D₁ D₂)
       (case+ {V = V} {M = M₁} {N = M₂} e₀ e₁ e₂) ceq st le =
    A₁ , A₂ , ih₀ , ih₁ , ih₂
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)
      A↑ = wkᵗ-v (wkᵗ-v A)
      t↑ = wkᵗ-e (wkᵗ-e t)
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})

      pΓ = co²ᵗ-ctx σ A₁ A₂ Γ
      pA = co²ᵗ-v   σ A₁ A₂ A
      pt = co²ᵗ-e   σ A₁ A₂ t
      pι = co²ᵗ-ˢ   ι σ A₁ A₂

      st↑ = subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st
      le↑ = subst (λ z → Q ⊩ _ ≾̂ₑ z) (sym pt) le

      ih₀ = cmpV ι↑ Γ↑ (α₁ |+| α₂) V D₀ (reV pι V e₀) (trans ceq (sym pΓ))
                 (<:̂ᵛ-refl _)
      ih₁ = cmpC ι↑ (Γ↑ ∷ α₁) A↑ t↑ M₁ D₁ (reC pι M₁ e₁)
                 (cong (_∷ A₁) (trans ceq (sym pΓ))) st↑ le↑
      ih₂ = cmpC ι↑ (Γ↑ ∷ α₂) A↑ t↑ M₂ D₂ (reC pι M₂ e₂)
                 (cong (_∷ A₂) (trans ceq (sym pΓ))) st↑ le↑

  -- primitive recursion on natural numbers
  --
  -- The result type and the effect are their own witnesses; the slack
  -- sits in the two atoms against the expected type and effect.

  cmpC {Θ = Θ} {σ = σ} {Q = Q} ι Γ A t _
       (recℕ {B = B} {ε = ε} D₀ D₁ D₂ it) (recℕ {V = V} {M = M₁} {N = M₂} e₀ e₁ e₂)
       ceq st le =
    B , ε , ih₀ , ih₁ , ih₂ , it ,
    subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st ,
    subst (λ z → Q ⊩ ε ≾̂ₑ z) (sym pt) le
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx Γ)
      β  = wkᵉ-v (tvar (newᵗ {Θ}))
      e  = evar (newᵉ {Θ +ty})

      pΓ = coᵗᵉ-ctx σ B ε Γ
      pA = coᵗᵉ-v   σ B ε A
      pt = coᵗᵉ-e   σ B ε t
      pι = coᵗᵉ-ˢ   ι σ B ε

      ih₀ = cmpV ι↑ Γ↑ Nat V D₀ (reV pι V e₀) (trans ceq (sym pΓ)) Natₛ
      ih₁ = cmpC ι↑ Γ↑ β e M₁ D₁ (reC pι M₁ e₁) (trans ceq (sym pΓ))
                 (<:̂ᵛ-refl _) ⊩≾̂ₑ-refl
      ih₂ = cmpC ι↑ ((Γ↑ ⟨ rconst ⊤ᵣ ⟩ ∷ Nat) ⟨ ∣ e ∣̂ᵉ ⟩ ∷ β) β e M₂ D₂ (reC pι M₂ e₂)
                 (cong (λ G → (G ⟨ rconst ⊤ᵣ ⟩ ∷ Nat) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B) (trans ceq (sym pΓ)))
                 (<:̂ᵛ-refl _) ⊩≾̂ₑ-refl

  -- list elimination
  --
  -- The element type is the scrutinee's own; the branches inherit the
  -- slack.

  cmpC {Θ = Θ} {σ = σ} {Q = Q} ι Γ A t _
       (caseL_`nil_`cons_ {A = A₁} D₀ D₁ D₂)
       (caseL {V = V} {M = M₁} {N = M₂} e₀ e₁ e₂) ceq st le =
    A₁ , ih₀ , ih₁ , ih₂
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      Γ↑ = wkᵗ-ctx Γ
      A↑ = wkᵗ-v A
      t↑ = wkᵗ-e t
      α  = tvar (newᵗ {Θ})

      pΓ = wk-,ᵗ-ctx σ A₁ Γ
      pA = wk-,ᵗ-v   σ A₁ A
      pt = wk-,ᵗ-e   σ A₁ t
      pι = wk-,ᵗ-ˢ   ι σ A₁

      st↑ = subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st
      le↑ = subst (λ z → Q ⊩ _ ≾̂ₑ z) (sym pt) le

      ih₀ = cmpV ι↑ Γ↑ (|List| α) V D₀ (reV pι V e₀) (trans ceq (sym pΓ))
                 (<:̂ᵛ-refl _)
      ih₁ = cmpC ι↑ Γ↑ A↑ t↑ M₁ D₁ (reC pι M₁ e₁) (trans ceq (sym pΓ)) st↑ le↑
      ih₂ = cmpC ι↑ (Γ↑ ∷ α ∷ |List| α) A↑ t↑ M₂ D₂ (reC pι M₂ e₂)
                 (cong (λ G → G ∷ A₁ ∷ |List| A₁) (trans ceq (sym pΓ))) st↑ le↑

  -- primitive recursion on lists
  --
  -- As for `recℕ`, with the scrutinee's element type as a further
  -- witness.

  cmpC {Θ = Θ} {σ = σ} {Q = Q} ι Γ A t _
       (recL {A = A₁} {B = B} {ε = ε} D₀ D₁ D₂ it) (recL {V = V} {M = M₁} {N = M₂} e₀ e₁ e₂)
       ceq st le =
    A₁ , B , ε , ih₀ , ih₁ , ih₂ , it ,
    subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st ,
    subst (λ z → Q ⊩ ε ≾̂ₑ z) (sym pt) le
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))
      α  = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      β  = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})

      pΓ = co²ᵗᵉ-ctx σ A₁ B ε Γ
      pA = co²ᵗᵉ-v   σ A₁ B ε A
      pt = co²ᵗᵉ-e   σ A₁ B ε t
      pι = co²ᵗᵉ-ˢ   ι σ A₁ B ε

      ih₀ = cmpV ι↑ Γ↑ (|List| α) V D₀ (reV pι V e₀) (trans ceq (sym pΓ)) (<:̂ᵛ-refl _)
      ih₁ = cmpC ι↑ Γ↑ β e M₁ D₁ (reC pι M₁ e₁) (trans ceq (sym pΓ))
                 (<:̂ᵛ-refl _) ⊩≾̂ₑ-refl
      ih₂ = cmpC ι↑ ((Γ↑ ⟨ rconst ⊤ᵣ ⟩ ∷ α ∷ |List| α) ⟨ ∣ e ∣̂ᵉ ⟩ ∷ β) β e M₂ D₂ (reC pι M₂ e₂)
                 (cong (λ G → (G ⟨ rconst ⊤ᵣ ⟩ ∷ A₁ ∷ |List| A₁) ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ B)
                       (trans ceq (sym pΓ)))
                 (<:̂ᵛ-refl _) ⊩≾̂ₑ-refl

  -- performing algebraic operations

  cmpC {Θ = Θ} {σ = σ} {Q = Q} ι Γ A t _
       (perform {ε = ε} op D₁ D₂) (perform {V = V} {M = M} e₁ e₂) ceq st le =
    ε , ih₁ , ih₂ ,
    subst (λ z → Q ⊩ econst (op-grade op) ·̂ₑ ε ≾̂ₑ z) (sym pt) le
    where
      ι↑ = ι ⨟ˢ wkˢᵉ
      σ' = σ ,ᵉ ε
      Γ↑ = wkᵉ-ctx Γ
      A↑ = wkᵉ-v A
      e  = evar (newᵉ {Θ})

      pΓ = wk-,ᵉ-ctx σ ε Γ
      pA = wk-,ᵉ-v   σ ε A
      pt = wk-,ᵉ-e   σ ε t
      pι = wk-,ᵉ-ˢ   ι σ ε

      ih₁ = cmpV ι↑ Γ↑ ⌜ param op ⌝ᵍ V D₁ (reV pι V e₁) (trans ceq (sym pΓ))
                 (subst (λ z → Q ∣ ⌜ param op ⌝ᵍ <:̂ᵛ z)
                        (sym (⌜⌝ᵍ-subst σ' (param op)))
                        (<:̂ᵛ-refl ⌜ param op ⌝ᵍ))
      ih₂ = cmpC ι↑ (Γ↑ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ) A↑ e M D₂
                 (reC pι M e₂)
                 (cong₂ (λ G Z → G ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ Z)
                        (trans ceq (sym pΓ))
                        (sym (⌜⌝ᵍ-subst σ' (arity op))))
                 (subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st) ⊩≾̂ₑ-refl

  -- explicit delaying of a computation

  cmpC {Θ = Θ} {σ = σ} {Q = Q} ι Γ A t _ (delay {ε = ε} τ D) (delay {M = M} e') ceq st le =
    ε , ih , subst (λ z → Q ⊩ econst (of-durᵉ τ) ·̂ₑ ε ≾̂ₑ z) (sym pt) le
    where
      ι↑ = ι ⨟ˢ wkˢᵉ
      Γ↑ = wkᵉ-ctx Γ
      A↑ = wkᵉ-v A
      e  = evar (newᵉ {Θ})

      pΓ = wk-,ᵉ-ctx σ ε Γ
      pA = wk-,ᵉ-v   σ ε A
      pt = wk-,ᵉ-e   σ ε t
      pι = wk-,ᵉ-ˢ   ι σ ε

      ih = cmpC ι↑ (Γ↑ ⟨ rconst (of-durʳ τ) ⟩) A↑ e M D (reC pι M e')
                (cong (_⟨ rconst (of-durʳ τ) ⟩) (trans ceq (sym pΓ)))
                (subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st) ⊩≾̂ₑ-refl

  -- effect handling
  --
  -- The handled computation's type and the handler's result type are
  -- their own witnesses; the slack sits in the subtyping atom.

  cmpC {Θ = Θ} {σ = σ} {Q = Q} ι Γ A t _
       (handle_`with_ {A = A₁} {B = A₂} {ε = ε₁} {ε' = ε₂} D₁ DV)
       (handle {M = M} {V = V} eM eV) ceq st le =
    A₁ , A₂ , ε₁ , ε₂ , ih₁ , ihV ,
    subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st ,
    subst (λ z → Q ⊩ ε₁ ·̂ₑ ε₂ ≾̂ₑ z) (sym pt) le
    where
      ι↑  = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ ⨟ˢ wkˢᵉ
      Γ↑  = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ)))
      α   = wkᵉ-v (wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ}))))
      γ   = wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ +ty})))
      e₁  = wkᵉ-e (evar (newᵉ {Θ +ty +ty}))
      e₂  = evar (newᵉ {Θ +ty +ty +e})

      pΓ  = co²ᵗ²ᵉ-ctx  σ A₁ A₂ ε₁ ε₂ Γ
      pA  = co²ᵗ²ᵉ-v    σ A₁ A₂ ε₁ ε₂ A
      pt  = co²ᵗ²ᵉ-e    σ A₁ A₂ ε₁ ε₂ t
      pι  = co²ᵗ²ᵉ-ˢ    ι σ A₁ A₂ ε₁ ε₂

      ih₁ = cmpC ι↑ Γ↑ α e₁ M D₁ (reC pι M eM) (trans ceq (sym pΓ))
                 (<:̂ᵛ-refl _) ⊩≾̂ₑ-refl
      ihV = cmpV ι↑ Γ↑ ((α ‼ e₁) ⇛ (γ ‼ e₂)) V DV (reV pι V eV) (trans ceq (sym pΓ))
                 (<:̂ᵛ-refl _)

  -- unboxing a resource value
  --
  -- The witnesses are the payload and the grade the value reaches.

  cmpC {Θ = Θ} {σ = σ} {Q = Q} ι Γ A t _
       (unbox {X = A₂} {ρ = ρ₁} R ok D) (unbox {V = V} {N = N} eV eN)
       ceq st le =
    A₂ , ρ₁ , sres ,
    ⊨-≐ᵥ σ' (resTy ι↑ Γ↑ V) ([ r ] β) ety ,
    subst (λ g → Q ⊩ g ≾̂ᵣ ρ₁) (sym egr) ok , ih
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢʳ
      σ' = σ ,ᵗ A₂ ,ʳ ρ₁
      Γ↑ = wkʳ-ctx (wkᵗ-ctx Γ)
      A↑ = wkʳ-v (wkᵗ-v A)
      t↑ = wkʳ-e (wkᵗ-e t)
      β  = wkʳ-v (tvar (newᵗ {Θ}))
      r  = rvar (newʳ {Θ +ty})

      pΓ = coᵗʳ-ctx σ A₂ ρ₁ Γ
      pA = coᵗʳ-v   σ A₂ ρ₁ A
      pt = coᵗʳ-e   σ A₂ ρ₁ t
      pι = coᵗʳ-ˢ   ι σ A₂ ρ₁

      c = cmpR {σ = σ'} ι↑ Γ↑ V R (reV pι V eV) (trans ceq (sym pΓ))

      sres = proj₁ c
      ety = proj₁ (proj₂ c)
      egr = proj₂ (proj₂ c)

      ih = cmpC ι↑ (Γ↑ ∷ β) A↑ t↑ N D (reC pι N eN)
                (cong (_∷ A₂) (trans ceq (sym pΓ)))
                (subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st)
                (subst (λ z → Q ⊩ _ ≾̂ₑ z) (sym pt) le)

  -- boxing up a value
  --
  -- The grade is the annotation's instance; only the payload's type is a
  -- witness.

  cmpC {Θ = Θ} {σ = σ} {Q = Q} ι Γ A t _ (box {A = A₁} ρ D₁ D₂)
       (box {ρ = ρ₀} {V = V} {N = N} eρ eV eN) ceq st le =
    A₁ , ih₁ , ih₂
    where
      ι↑ = ι ⨟ˢ wkˢᵗ
      σ' = σ ,ᵗ A₁
      Γ↑ = wkᵗ-ctx Γ
      A↑ = wkᵗ-v A
      t↑ = wkᵗ-e t
      α  = tvar (newᵗ {Θ})
      r  = ρ₀ [ ι↑ ]ʳ

      pΓ = wk-,ᵗ-ctx σ A₁ Γ
      pA = wk-,ᵗ-v   σ A₁ A
      pt = wk-,ᵗ-e   σ A₁ t
      pι = wk-,ᵗ-ˢ   ι σ A₁

      pr : r [ σ' ]ʳ ≡ ρ
      pr = trans ([⨟]ʳ ρ₀ ι↑ σ') (trans ([≐]ʳ pι ρ₀) eρ)

      ih₁ = cmpV ι↑ (Γ↑ ⟨ r ⟩) α V D₁ (reV pι V eV)
                 (cong₂ _⟨_⟩ (trans ceq (sym pΓ)) (sym pr)) (<:̂ᵛ-refl _)
      ih₂ = cmpC ι↑ (Γ↑ ∷ [ r ] α) A↑ t↑ N D₂ (reC pι N eN)
                 (cong₂ (λ G z → G ∷ [ z ] A₁) (trans ceq (sym pΓ)) (sym pr))
                 (subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st)
                 (subst (λ z → Q ⊩ _ ≾̂ₑ z) (sym pt) le)

  -- type annotation
  --
  -- As for values, the slack sits in the two atoms.

  cmpC {σ = σ} {Q = Q} ι Γ A t _ {A₀ = A₀} {ε₀ = ε₀} (annᶜ _ D)
       (annᶜ {M = M} {A = B} {ε = u} eM eB eu) ceq st le =
    cmpC ι Γ (B [ ι ]ᵛ) (u [ ι ]ᵉ) M D (invC M eM) ceq
         (subst (λ z → Q ∣ A₀ <:̂ᵛ z) (sym pB) (<:̂ᵛ-refl A₀))
         (subst (λ z → Q ⊩ ε₀ ≾̂ₑ z) (sym pu) ⊩≾̂ₑ-refl) ,
    subst (λ z → Q ∣ z <:̂ᵛ A [ σ ]ᵛ) (sym pB) st ,
    subst (λ z → Q ⊩ z ≾̂ₑ t [ σ ]ᵉ) (sym pu) le
    where
      pB : B [ ι ]ᵛ [ σ ]ᵛ ≡ A₀
      pB = trans ([⨟]ᵛ B ι σ) eB

      pu : u [ ι ]ᵉ [ σ ]ᵉ ≡ ε₀
      pu = trans ([⨟]ᵉ u ι σ) eu

  -- subsumption
  --
  -- Invisible to erasure; its two witnesses compose with the slack.

  cmpC ι Γ A t M (subC D (p ‼ₛ q)) inv ceq st le =
    cmpC ι Γ A t M D inv ceq (<:̂ᵛ-trans p st) (transₑ q le)

-- Completeness: a derivation erasing to an instance of the raw term
-- satisfies the constraint generated from the term.

completeVˢ : ∀ {Θ₀ Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {Γ₀ : OCtx Θ' n}
           → (ι : Subst Θ₀ Θ) → (Γ : OCtx Θ n) → (A : OVType Θ) → (V : RawV Θ₀ n)
           → {A₀ : OVType Θ'}
           → (D : Q ∣ Γ₀ ⊢V⦂ A₀)
           → ⌊ D ⌋ᵛ ≡ V [ ι ⨟ˢ σ ]ᴿᵛ
           → Γ₀ ≡ Γ [ σ ]ᶜᵗˣ
           → Q ∣ A₀ <:̂ᵛ A [ σ ]ᵛ
           --------------------------
           → σ ⊨[ Q ] genVˢ ι Γ V A

completeVˢ ι Γ A V D e = cmpV ι Γ A V D (invV V (sym e))

completeCˢ : ∀ {Θ₀ Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {Γ₀ : OCtx Θ' n}
           → (ι : Subst Θ₀ Θ) → (Γ : OCtx Θ n) → (A : OVType Θ) → (t : EExp Θ)
           → (M : RawC Θ₀ n)
           → {A₀ : OVType Θ'} → {ε₀ : EExp Θ'}
           → (D : Q ∣ Γ₀ ⊢C⦂ A₀ ‼ ε₀)
           → ⌊ D ⌋ᶜ ≡ M [ ι ⨟ˢ σ ]ᴿᶜ
           → Γ₀ ≡ Γ [ σ ]ᶜᵗˣ
           → Q ∣ A₀ <:̂ᵛ A [ σ ]ᵛ
           → Q ⊩ ε₀ ≾̂ₑ t [ σ ]ᵉ
           --------------------------------
           → σ ⊨[ Q ] genCˢ ι Γ M (A ‼ t)

completeCˢ ι Γ A t M D e = cmpC ι Γ A t M D (invC M (sym e))

-- Generation for a raw term over the scope of the context

completeV : ∀ {Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {Γ₀ : OCtx Θ' n}
          → (Γ : OCtx Θ n) → (A : OVType Θ) → (V : RawV Θ n)
          → {A₀ : OVType Θ'}
          → (D : Q ∣ Γ₀ ⊢V⦂ A₀)
          → ⌊ D ⌋ᵛ ≡ V [ σ ]ᴿᵛ
          → Γ₀ ≡ Γ [ σ ]ᶜᵗˣ
          → Q ∣ A₀ <:̂ᵛ A [ σ ]ᵛ
          --------------------------
          → σ ⊨[ Q ] genV Γ V A

completeV {σ = σ} Γ A V D e =
  completeVˢ idˢ Γ A V D (trans e (sym ([≐]ᴿᵛ (⨟-idˡ σ) V)))

completeC : ∀ {Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {Γ₀ : OCtx Θ' n}
          → (Γ : OCtx Θ n) → (A : OVType Θ) → (t : EExp Θ) → (M : RawC Θ n)
          → {A₀ : OVType Θ'} → {ε₀ : EExp Θ'}
          → (D : Q ∣ Γ₀ ⊢C⦂ A₀ ‼ ε₀)
          → ⌊ D ⌋ᶜ ≡ M [ σ ]ᴿᶜ
          → Γ₀ ≡ Γ [ σ ]ᶜᵗˣ
          → Q ∣ A₀ <:̂ᵛ A [ σ ]ᵛ
          → Q ⊩ ε₀ ≾̂ₑ t [ σ ]ᵉ
          --------------------------------
          → σ ⊨[ Q ] genC Γ M (A ‼ t)

completeC {σ = σ} Γ A t M D e =
  completeCˢ idˢ Γ A t M D (trans e (sym ([≐]ᴿᶜ (⨟-idˡ σ) M)))

-- Satisfying the generated constraint is equivalent to erasing, from a
-- derivation, to the instance of the raw term.

charV : ∀ {Θ n Θ'} → (Γ : OCtx Θ n) → (V : RawV Θ n) → (A : OVType Θ)
      → (σ : Subst Θ Θ') → (Q : Hyps Θ')
      ----------------------------------------------------------------
      → (σ ⊨[ Q ] genV Γ V A)
        ⇔ (Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢V⦂ A [ σ ]ᵛ) ] (⌊ D ⌋ᵛ ≡ V [ σ ]ᴿᵛ))

charV Γ V A σ Q =
  mk⇔ (soundV Γ V A)
      (λ { (D , e) → completeV Γ A V D e refl (<:̂ᵛ-refl (A [ σ ]ᵛ)) })

charC : ∀ {Θ n Θ'} → (Γ : OCtx Θ n) → (M : RawC Θ n) → (A : OVType Θ)
      → (t : EExp Θ) → (σ : Subst Θ Θ') → (Q : Hyps Θ')
      ------------------------------------------------------------------------
      → (σ ⊨[ Q ] genC Γ M (A ‼ t))
        ⇔ (Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢C⦂ A [ σ ]ᵛ ‼ t [ σ ]ᵉ) ] (⌊ D ⌋ᶜ ≡ M [ σ ]ᴿᶜ))

charC Γ M A t σ Q =
  mk⇔ (soundC Γ M A t)
      (λ { (D , e) → completeC Γ A t M D e refl (<:̂ᵛ-refl (A [ σ ]ᵛ)) ⊩≾̂ₑ-refl })

-- Sanity checks: completeness computes on examples.

private

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  -- a `return` with slack absorbed: the generated `≾̂ₑᶜ` is the hypothesis

  ex-return : idˢ ⊨[ ∅ᴴ ] genC (∅ᶜ ∷ Unit) (return ⋆) (Unit ‼ ûₑ)
  ex-return = completeC {σ = idˢ} (∅ᶜ ∷ Unit) Unit ûₑ (return ⋆) (return ⋆) refl refl
                        Unitₛ ⊩≾̂ₑ-refl

  -- a subsumption erases away, and completeness sees the same constraint

  ex-sub : idˢ ⊨[ ∅ᴴ ] genC (∅ᶜ ∷ Unit) (return ⋆) (Unit ‼ ûₑ)
  ex-sub = completeC {σ = idˢ} (∅ᶜ ∷ Unit) Unit ûₑ (return ⋆)
                     (coerce ⊩≾̂ₑ-refl (return ⋆)) refl refl Unitₛ ⊩≾̂ₑ-refl

  -- a variable typed at a supertype: the atom is the subsumption's witness

  ex-var : idˢ ⊨[ ∅ᴴ ] genV (∅ᶜ ∷ [ ûᵣ ] Unit) (var zero) ([ ûᵣ ] Unit)
  ex-var = completeV {σ = idˢ} (∅ᶜ ∷ [ ûᵣ ] Unit) ([ ûᵣ ] Unit) (var zero)
                     (subV (var Hd (≾ᵘ-ok ⊩≾̂ᵣ-refl)) (<:̂ᵛ-refl ([ ûᵣ ] Unit)))
                     refl refl (<:̂ᵛ-refl ([ ûᵣ ] Unit))

  -- unboxing a boxed variable: the gate is `false`, the row is inhabited

  ex-unbox : idˢ ⊨[ ∅ᴴ ] genC (∅ᶜ ∷ [ ûᵣ ] Unit) (unbox (var zero) (return ⋆))
                              (Unit ‼ ûₑ)
  ex-unbox = completeC {σ = idˢ} (∅ᶜ ∷ [ ûᵣ ] Unit) Unit ûₑ (unbox (var zero) (return ⋆))
                       (unbox (res-var {z = Hd}) ⊩≾̂ᵣ-refl (return ⋆))
                       refl refl Unitₛ ⊩≾̂ₑ-refl

  -- unboxing an annotated variable: the annotation's atom is the step's

  ex-unbox-ann : idˢ ⊨[ ∅ᴴ ] genC (∅ᶜ ∷ [ ûᵣ ] Unit)
                                  (unbox (var zero ⦂ᵛ [ ûᵣ ] Unit) (return ⋆)) (Unit ‼ ûₑ)
  ex-unbox-ann =
    completeC {σ = idˢ} (∅ᶜ ∷ [ ûᵣ ] Unit) Unit ûₑ (unbox (var zero ⦂ᵛ [ ûᵣ ] Unit) (return ⋆))
              (unbox (res-ann ûᵣ Unit (res-var {z = Hd}) ⊩≾̂ᵣ-refl Unitₛ) ⊩≾̂ᵣ-refl (return ⋆))
              refl refl Unitₛ ⊩≾̂ₑ-refl

  -- boxing a value: the annotation needs no witness, only the payload's type

  ex-box : idˢ ⊨[ ∅ᴴ ] genC ∅ᶜ (box ûᵣ ⋆ (return ⋆)) (Unit ‼ ûₑ)
  ex-box = completeC {σ = idˢ} ∅ᶜ Unit ûₑ (box ûᵣ ⋆ (return ⋆))
                     (box ûᵣ ⋆ (return ⋆)) refl refl Unitₛ ⊩≾̂ₑ-refl

  ex-box-is : ex-box ≡ (Unit , ((Unitₛ , Unitₛ) , ((Unitₛ , Unitₛ) , ⊩≾̂ₑ-refl)))
  ex-box-is = refl
