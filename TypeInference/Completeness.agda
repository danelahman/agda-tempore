------------------------------------------------------------------
-- Completeness of constraint generation: a derivation erasing to --
-- an instance of a raw term satisfies, along that instance, the  --
-- constraint generated from the term.                            --
--                                                                --
-- The expected type is an upper bound, so the hypotheses are a   --
-- subtyping and a grade ordering, not equations: subsumption is  --
-- invisible to erasure and composes into them.                   --
------------------------------------------------------------------

open import Data.Fin using (zero)
open import Data.Product using (Σ-syntax; _,_)

open import Function.Bundles using (_⇔_; mk⇔)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Completeness (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades         S
open import TypeInference.OpenSyntax.Types          S
open import TypeInference.OpenSyntax.Contexts       S
open import TypeInference.OpenSyntax.ContextsLemmas S
open import TypeInference.OpenSyntax.Subst          S
open import TypeInference.OpenSyntax.Hyps           S
open import TypeInference.OpenSyntax.Language       S

open import TypeInference.Raw.Syntax S
open import TypeInference.Raw.Subst  S
open import TypeInference.Erase      S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S

open import TypeInference.Generate  S
open import TypeInference.Soundness S

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

  -- base-typed constants, unit, booleans
  --
  -- None has a proper supertype, so the pin is recovered by inversion.

  cmpV ι Γ A _ (const B c) const ceq st = sym (<:̂ᵛ-Baseˡ st)
  cmpV ι Γ A _ ⋆           ⋆     ceq st = sym (<:̂ᵛ-Unitˡ st)
  cmpV ι Γ A _ true        true  ceq st = sym (<:̂ᵛ-Boolˡ st)
  cmpV ι Γ A _ false       false ceq st = sym (<:̂ᵛ-Boolˡ st)

  -- pairing
  --
  -- A supertype of a product is a product, so the slack splits between
  -- the two components.

  cmpV {Θ = Θ} {σ = σ} ι Γ A _ (⦉_,_⦊ {A = A₁} {B = A₂} D₁ D₂)
       (⦉_,_⦊ {V = V₁} {W = V₂} e₁ e₂) ceq st
    with <:̂ᵛ-×ˡ st
  ... | B₁ , B₂ , eq , st₁ , st₂ =
    B₁ , B₂ , trans (sym eq) (sym pA) , ih₁ , ih₂
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

  -- lambda abstraction with an annotated argument
  --
  -- The recorded annotation is the instance of the raw one, so the binder's
  -- type needs no witness.

  cmpV {Θ = Θ} {σ = σ} {Q = Q} ι Γ A _
       (lamᵃ A₁ {C = A₂ ‼ ε₀} D) (lamᵃ {A = B} {M = M} eB e) ceq st =
    A₂ , ε₀ , subst₂ (λ X Y → Q ∣ X ⇒ A₂ ‼ ε₀ <:̂ᵛ Y) (sym pB) (sym pA) st , ih
    where
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵉ
      σ' = σ ,ᵗ A₂ ,ᵉ ε₀
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx Γ)
      B' = B [ ι↑ ]ᵛ
      α  = wkᵉ-v (tvar (newᵗ {Θ}))
      e₀ = evar (newᵉ {Θ +ty})

      pΓ = coᵗᵉ-ctx σ A₂ ε₀ Γ
      pA = coᵗᵉ-v   σ A₂ ε₀ A
      pι = coᵗᵉ-ˢ   ι σ A₂ ε₀

      pB : B' [ σ' ]ᵛ ≡ A₁
      pB = trans ([⨟]ᵛ B ι↑ σ') (trans ([≐]ᵛ pι B) eB)

      ih = cmpC ι↑ (Γ↑ ∷ B') α e₀ M D (reC pι M e)
                (cong₂ _∷_ (trans ceq (sym pΓ)) (sym pB)) (<:̂ᵛ-refl _) ⊩≾̂ₑ-refl

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
    ε , ih , subst (λ z → Q ⊩ econst (of-natᵉ τ) ·̂ₑ ε ≾̂ₑ z) (sym pt) le
    where
      ι↑ = ι ⨟ˢ wkˢᵉ
      Γ↑ = wkᵉ-ctx Γ
      A↑ = wkᵉ-v A
      e  = evar (newᵉ {Θ})

      pΓ = wk-,ᵉ-ctx σ ε Γ
      pA = wk-,ᵉ-v   σ ε A
      pt = wk-,ᵉ-e   σ ε t
      pι = wk-,ᵉ-ˢ   ι σ ε

      ih = cmpC ι↑ (Γ↑ ⟨ rconst (of-natʳ τ) ⟩) A↑ e M D (reC pι M e')
                (cong (_⟨ rconst (of-natʳ τ) ⟩) (trans ceq (sym pΓ)))
                (subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st) ⊩≾̂ₑ-refl

  -- effect handling
  --
  -- The clause family is handled pointwise; only the clause context's
  -- weakenings and the two ground-type embeddings need collapsing. The
  -- handled result type is its own witness, so clauses and continuation
  -- are both typed at it and the slack sits in the one subtyping atom.

  cmpC {Θ = Θ} {Θ' = Θ'} {σ = σ} {Q = Q} ι Γ A t _
       (handle_`with_`in {A = A₁} {B = A₂} {ε = ε₁} {ε' = ε₂} D₁ H D₂)
       (handle {M = M} {H = R} {N = N} eM eR eN) ceq st le =
    A₁ , A₂ , ε₁ , ε₂ , ih₁ , ih₂ ,
    subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st ,
    subst (λ z → Q ⊩ ε₁ ·̂ₑ ε₂ ≾̂ₑ z) (sym pt) le , ihH
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
      pt  = co²ᵗ²ᵉ-e    σ A₁ A₂ ε₁ ε₂ t
      pΓ⇑ = co²ᵗ²ᵉ-ctx↑ σ A₁ A₂ ε₁ ε₂ Γ
      pγ⇑ = wk-↑ᵉ-v σ' γ
      pι  = co²ᵗ²ᵉ-ˢ    ι σ A₁ A₂ ε₁ ε₂
      pι⇑ = co²ᵗ²ᵉ-ˢ↑   ι σ A₁ A₂ ε₁ ε₂

      ih₁ = cmpC ι↑ Γ↑ α e₁ M D₁ (reC pι M eM) (trans ceq (sym pΓ))
                 (<:̂ᵛ-refl _) ⊩≾̂ₑ-refl
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

  -- unboxing a boxed variable

  cmpC {Θ = Θ} {σ = σ} {Q = Q} ι Γ A t _
       (unbox {A = A₂} {A₀ = A₁} {ρ₀ = ρ₀} {ρ' = ρ'} x ok sb D) (unbox {N = N} e')
       ceq st le =
    A₁ , A₂ , ρ₀ , lty , subst (λ z → Q ⊩ z ≾̂ᵣ ρ₀) (sym lgr) ok , sb , ih
    where
      i  = var-pos x
      ι↑ = ι ⨟ˢ wkˢᵗ ⨟ˢ wkˢᵗ ⨟ˢ wkˢʳ
      σ' = σ ,ᵗ A₁ ,ᵗ A₂ ,ʳ ρ₀
      Γ↑ = wkʳ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))
      A↑ = wkʳ-v (wkᵗ-v (wkᵗ-v A))
      t↑ = wkʳ-e (wkᵗ-e (wkᵗ-e t))
      β  = wkʳ-v (tvar (newᵗ {Θ +ty}))

      pΓ = co²ᵗʳ-ctx σ A₁ A₂ ρ₀ Γ
      pA = co²ᵗʳ-v   σ A₁ A₂ ρ₀ A
      pt = co²ᵗʳ-e   σ A₁ A₂ ρ₀ t
      pι = co²ᵗʳ-ˢ   ι σ A₁ A₂ ρ₀

      -- lookup in the weakened context, instantiated, is lookup in `Γ₀`

      lty : lookup-ty Γ↑ i [ σ' ]ᵛ ≡ [ ρ₀ ] A₁
      lty = trans (cong (_[ σ' ]ᵛ)
                        (trans (lookup-ty-wkʳ (wkᵗ-ctx (wkᵗ-ctx Γ)) i)
                               (cong wkʳ-v
                                     (trans (lookup-ty-wkᵗ (wkᵗ-ctx Γ) i)
                                            (cong wkᵗ-v (lookup-ty-wkᵗ Γ i))))))
            (trans (co²ᵗʳ-v σ A₁ A₂ ρ₀ (lookup-ty Γ i))
            (trans (sym (lookup-ty-subst Γ σ i))
            (trans (cong (λ G → lookup-ty G i) (sym ceq)) (var-pos-ty x))))

      lgr : lookup-gr Γ↑ i [ σ' ]ʳ ≡ ρ'
      lgr = trans (cong (_[ σ' ]ʳ)
                        (trans (lookup-gr-wkʳ (wkᵗ-ctx (wkᵗ-ctx Γ)) i)
                               (cong wkʳ-r
                                     (trans (lookup-gr-wkᵗ (wkᵗ-ctx Γ) i)
                                            (cong wkᵗ-r (lookup-gr-wkᵗ Γ i))))))
            (trans (co²ᵗʳ-r σ A₁ A₂ ρ₀ (lookup-gr Γ i))
            (trans (sym (lookup-gr-subst Γ σ i))
            (trans (cong (λ G → lookup-gr G i) (sym ceq)) (var-pos-gr x))))

      ih = cmpC ι↑ (Γ↑ ∷ β) A↑ t↑ N D (reC pι N e')
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

  ex-unbox : idˢ ⊨[ ∅ᴴ ] genC (∅ᶜ ∷ [ ûᵣ ] Unit) (unbox zero (return ⋆))
                              (Unit ‼ ûₑ)
  ex-unbox = completeC {σ = idˢ} (∅ᶜ ∷ [ ûᵣ ] Unit) Unit ûₑ (unbox zero (return ⋆))
                       (unbox Hd ⊩≾̂ᵣ-refl (<:̂ᵛ-refl Unit) (return ⋆))
                       refl refl Unitₛ ⊩≾̂ₑ-refl

  -- boxing a value: the annotation needs no witness, only the payload's type

  ex-box : idˢ ⊨[ ∅ᴴ ] genC ∅ᶜ (box ûᵣ ⋆ (return ⋆)) (Unit ‼ ûₑ)
  ex-box = completeC {σ = idˢ} ∅ᶜ Unit ûₑ (box ûᵣ ⋆ (return ⋆))
                     (box ûᵣ ⋆ (return ⋆)) refl refl Unitₛ ⊩≾̂ₑ-refl

  ex-box-is : ex-box ≡ (Unit , (refl , (refl , ⊩≾̂ₑ-refl)))
  ex-box-is = refl
