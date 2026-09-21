------------------------------------------------------------------
-- Completeness of constraint generation: a derivation            --
-- satisfies the constraint generated from its own erasure.       --
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
open import TypeInference.Erase      S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S

open import TypeInference.Generate  S
open import TypeInference.Soundness S

mutual

  completeV : ∀ {Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {Γ₀ : OCtx Θ' n}
            → (Γ : OCtx Θ n) → (A : OVType Θ)
            → {A₀ : OVType Θ'}
            → (D : Q ∣ Γ₀ ⊢V⦂ A₀)
            → Γ₀ ≡ Γ [ σ ]ᶜᵗˣ
            → Q ∣ A₀ <:̂ᵛ A [ σ ]ᵛ
            --------------------------
            → σ ⊨[ Q ] genV Γ ⌊ D ⌋ᵛ A

  -- variables
  --
  -- The raw index is `var-pos x`, at which the two lookups agree with the
  -- type and the grade of `x` itself.

  completeV {σ = σ} {Q = Q} Γ A (var {A = A₁} {ρ = ρ₁} x ok) ceq st =
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

  completeV Γ A (const B c) ceq st = sym (<:̂ᵛ-Baseˡ st)
  completeV Γ A ⋆           ceq st = sym (<:̂ᵛ-Unitˡ st)
  completeV Γ A true        ceq st = sym (<:̂ᵛ-Boolˡ st)
  completeV Γ A false       ceq st = sym (<:̂ᵛ-Boolˡ st)

  -- pairing
  --
  -- A supertype of a product is a product, so the slack splits between
  -- the two components.

  completeV {Θ = Θ} {σ = σ} Γ A (⦉_,_⦊ {A = A₁} {B = A₂} D₁ D₂) ceq st
    with <:̂ᵛ-×ˡ st
  ... | B₁ , B₂ , eq , st₁ , st₂ =
    B₁ , B₂ , trans (sym eq) (sym pA) , ih₁ , ih₂
    where
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})

      pΓ = co²ᵗ-ctx σ B₁ B₂ Γ
      pA = co²ᵗ-v   σ B₁ B₂ A

      ih₁ = completeV Γ↑ α₁ D₁ (trans ceq (sym pΓ)) st₁
      ih₂ = completeV Γ↑ α₂ D₂ (trans ceq (sym pΓ)) st₂

  -- lambda abstraction

  completeV {Θ = Θ} {σ = σ} {Q = Q} Γ A
            (lam {A = A₁} {C = A₂ ‼ ε₀} D) ceq st =
    A₁ , A₂ , ε₀ , subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st , ih
    where
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))
      α₁ = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      α₂ = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})

      pΓ = co²ᵗᵉ-ctx σ A₁ A₂ ε₀ Γ
      pA = co²ᵗᵉ-v   σ A₁ A₂ ε₀ A

      ih = completeC (Γ↑ ∷ α₁) α₂ e D
                     (cong (_∷ A₁) (trans ceq (sym pΓ))) (<:̂ᵛ-refl _) ⊩≾̂ₑ-refl

  -- subsumption
  --
  -- Invisible to erasure; its witness composes with the slack.

  completeV Γ A (subV D p) ceq st = completeV Γ A D ceq (<:̂ᵛ-trans p st)


  completeC : ∀ {Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {Γ₀ : OCtx Θ' n}
            → (Γ : OCtx Θ n) → (A : OVType Θ) → (t : EExp Θ)
            → {A₀ : OVType Θ'} → {ε₀ : EExp Θ'}
            → (D : Q ∣ Γ₀ ⊢C⦂ A₀ ‼ ε₀)
            → Γ₀ ≡ Γ [ σ ]ᶜᵗˣ
            → Q ∣ A₀ <:̂ᵛ A [ σ ]ᵛ
            → Q ⊩ ε₀ ≾̂ₑ t [ σ ]ᵉ
            --------------------------------
            → σ ⊨[ Q ] genC Γ ⌊ D ⌋ᶜ (A ‼ t)

  -- returning a value

  completeC Γ A t (return D) ceq st le = completeV Γ A D ceq st , le

  -- sequential composition
  --
  -- The witnesses make the continuation's context an instance of the
  -- generated one on the nose: `∣ e₁ ∣̂ᵉ` instantiates to `∣ ε₁ ∣̂ᵉ`.

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t
            (_⨟_ {A = A₁} {ε' = ε₂} {ε = ε₁} D₁ D₂) ceq st le =
    A₁ , ε₁ , ε₂ , ih₁ , ih₂ , subst (λ z → Q ⊩ ε₁ ·̂ₑ ε₂ ≾̂ₑ z) (sym pt) le
    where
      Γ↑ = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx Γ))
      A↑ = wkᵉ-v (wkᵉ-v (wkᵗ-v A))
      α  = wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ})))
      e₁ = wkᵉ-e (evar (newᵉ {Θ +ty}))
      e₂ = evar (newᵉ {Θ +ty +e})

      pΓ = coᵗ²ᵉ-ctx σ A₁ ε₁ ε₂ Γ
      pA = coᵗ²ᵉ-v   σ A₁ ε₁ ε₂ A
      pt = coᵗ²ᵉ-e   σ A₁ ε₁ ε₂ t

      ih₁ = completeC Γ↑ α e₁ D₁ (trans ceq (sym pΓ)) (<:̂ᵛ-refl _) ⊩≾̂ₑ-refl
      ih₂ = completeC (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) A↑ e₂ D₂
                      (cong (λ G → G ⟨ ∣ ε₁ ∣̂ᵉ ⟩ ∷ A₁) (trans ceq (sym pΓ)))
                      (subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st) ⊩≾̂ₑ-refl

  -- function application

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t
            (_·_ {A = A₁} {C = A₂ ‼ ε₀} D₁ D₂) ceq st le =
    A₁ , A₂ , ε₀ , ih₁ , ih₂ ,
    subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st ,
    subst (λ z → Q ⊩ ε₀ ≾̂ₑ z) (sym pt) le
    where
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))
      α  = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      β  = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})

      pΓ = co²ᵗᵉ-ctx σ A₁ A₂ ε₀ Γ
      pA = co²ᵗᵉ-v   σ A₁ A₂ ε₀ A
      pt = co²ᵗᵉ-e   σ A₁ A₂ ε₀ t

      ih₁ = completeV Γ↑ (α ⇒ (β ‼ e)) D₁ (trans ceq (sym pΓ)) (<:̂ᵛ-refl _)
      ih₂ = completeV Γ↑ α D₂ (trans ceq (sym pΓ)) (<:̂ᵛ-refl _)

  -- pattern-matching

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t
            (match_`in_ {A = A₁} {B = A₂} D₁ D₂) ceq st le =
    A₁ , A₂ , ih₁ , ih₂
    where
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)
      A↑ = wkᵗ-v (wkᵗ-v A)
      t↑ = wkᵗ-e (wkᵗ-e t)
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})

      pΓ = co²ᵗ-ctx σ A₁ A₂ Γ
      pA = co²ᵗ-v   σ A₁ A₂ A
      pt = co²ᵗ-e   σ A₁ A₂ t

      ih₁ = completeV Γ↑ (α₁ |×| α₂) D₁ (trans ceq (sym pΓ)) (<:̂ᵛ-refl _)
      ih₂ = completeC (Γ↑ ∷ α₁ ∷ α₂) A↑ t↑ D₂
                      (cong (λ G → G ∷ A₁ ∷ A₂) (trans ceq (sym pΓ)))
                      (subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st)
                      (subst (λ z → Q ⊩ _ ≾̂ₑ z) (sym pt) le)

  -- empty type elimination

  completeC Γ A t (absurd D) ceq st le = completeV Γ Empty D ceq Emptyₛ

  -- boolean elimination

  completeC Γ A t (if_`then_`else_ D₀ D₁ D₂) ceq st le =
    completeV Γ Bool D₀ ceq Boolₛ ,
    completeC Γ A t D₁ ceq st le ,
    completeC Γ A t D₂ ceq st le

  -- performing algebraic operations

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t
            (perform {ε = ε} op D₁ D₂) ceq st le =
    ε , ih₁ , ih₂ ,
    subst (λ z → Q ⊩ econst (op-grade op) ·̂ₑ ε ≾̂ₑ z) (sym pt) le
    where
      σ' = σ ,ᵉ ε
      Γ↑ = wkᵉ-ctx Γ
      A↑ = wkᵉ-v A
      e  = evar (newᵉ {Θ})

      pΓ = wk-,ᵉ-ctx σ ε Γ
      pA = wk-,ᵉ-v   σ ε A
      pt = wk-,ᵉ-e   σ ε t

      ih₁ = completeV Γ↑ ⌜ param op ⌝ᵍ D₁ (trans ceq (sym pΓ))
                      (subst (λ z → Q ∣ ⌜ param op ⌝ᵍ <:̂ᵛ z)
                             (sym (⌜⌝ᵍ-subst σ' (param op)))
                             (<:̂ᵛ-refl ⌜ param op ⌝ᵍ))
      ih₂ = completeC (Γ↑ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ) A↑ e D₂
                      (cong₂ (λ G Z → G ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ Z)
                             (trans ceq (sym pΓ))
                             (sym (⌜⌝ᵍ-subst σ' (arity op))))
                      (subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st) ⊩≾̂ₑ-refl

  -- explicit delaying of a computation

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t (delay {ε = ε} τ D) ceq st le =
    ε , ih , subst (λ z → Q ⊩ econst (of-natᵉ τ) ·̂ₑ ε ≾̂ₑ z) (sym pt) le
    where
      Γ↑ = wkᵉ-ctx Γ
      A↑ = wkᵉ-v A
      e  = evar (newᵉ {Θ})

      pΓ = wk-,ᵉ-ctx σ ε Γ
      pA = wk-,ᵉ-v   σ ε A
      pt = wk-,ᵉ-e   σ ε t

      ih = completeC (Γ↑ ⟨ rconst (of-natʳ τ) ⟩) A↑ e D
                     (cong (_⟨ rconst (of-natʳ τ) ⟩) (trans ceq (sym pΓ)))
                     (subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st) ⊩≾̂ₑ-refl

  -- effect handling
  --
  -- The clause family is handled pointwise; only the clause context's
  -- weakenings and the two ground-type embeddings need collapsing. The
  -- handled result type is its own witness, so clauses and continuation
  -- are both typed at it and the slack sits in the one subtyping atom.

  completeC {Θ = Θ} {Θ' = Θ'} {σ = σ} {Q = Q} Γ A t
            (handle_`with_`in {A = A₁} {B = A₂} {ε = ε₁} {ε' = ε₂} D₁ H D₂)
            ceq st le =
    A₁ , A₂ , ε₁ , ε₂ , ih₁ , ih₂ ,
    subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st ,
    subst (λ z → Q ⊩ ε₁ ·̂ₑ ε₂ ≾̂ₑ z) (sym pt) le , ihH
    where
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

      ih₁ = completeC Γ↑ α e₁ D₁ (trans ceq (sym pΓ)) (<:̂ᵛ-refl _) ⊩≾̂ₑ-refl
      ih₂ = completeC (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) γ e₂ D₂
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
        completeC (Γ⇑ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                      ∷ [ rconst (mapᵉ (op-grade op)) ] (⌜ arity op ⌝ᵍ ⇒ γ⇑ ‼ e''))
                  γ⇑ (econst (op-grade op) ·̂ₑ e'')
                  (H op) (cH op)
                  (subst (λ z → wkᵉ-H Q ∣ wkᵉ-v A₂ <:̂ᵛ z) (sym pγ⇑)
                         (<:̂ᵛ-refl (wkᵉ-v A₂)))
                  ⊩≾̂ₑ-refl

  -- unboxing a boxed variable

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t
            (unbox {A = A₂} {A₀ = A₁} {ρ₀ = ρ₀} {ρ' = ρ'} x ok sb D) ceq st le =
    A₁ , A₂ , ρ₀ , lty , subst (λ z → Q ⊩ z ≾̂ᵣ ρ₀) (sym lgr) ok , sb , ih
    where
      i  = var-pos x
      σ' = σ ,ᵗ A₁ ,ᵗ A₂ ,ʳ ρ₀
      Γ↑ = wkʳ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))
      A↑ = wkʳ-v (wkᵗ-v (wkᵗ-v A))
      t↑ = wkʳ-e (wkᵗ-e (wkᵗ-e t))
      β  = wkʳ-v (tvar (newᵗ {Θ +ty}))

      pΓ = co²ᵗʳ-ctx σ A₁ A₂ ρ₀ Γ
      pA = co²ᵗʳ-v   σ A₁ A₂ ρ₀ A
      pt = co²ᵗʳ-e   σ A₁ A₂ ρ₀ t

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

      ih = completeC (Γ↑ ∷ β) A↑ t↑ D
                     (cong (_∷ A₂) (trans ceq (sym pΓ)))
                     (subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st)
                     (subst (λ z → Q ⊩ _ ≾̂ₑ z) (sym pt) le)

  -- boxing up a value

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t (box {A = A₁} ρ D₁ D₂) ceq st le =
    A₁ , ρ , ih₁ , ih₂
    where
      Γ↑ = wkʳ-ctx (wkᵗ-ctx Γ)
      A↑ = wkʳ-v (wkᵗ-v A)
      t↑ = wkʳ-e (wkᵗ-e t)
      α  = wkʳ-v (tvar (newᵗ {Θ}))
      r  = rvar (newʳ {Θ +ty})

      pΓ = coᵗʳ-ctx σ A₁ ρ Γ
      pA = coᵗʳ-v   σ A₁ ρ A
      pt = coᵗʳ-e   σ A₁ ρ t

      ih₁ = completeV (Γ↑ ⟨ r ⟩) α D₁
                      (cong (_⟨ ρ ⟩) (trans ceq (sym pΓ))) (<:̂ᵛ-refl _)
      ih₂ = completeC (Γ↑ ∷ [ r ] α) A↑ t↑ D₂
                      (cong (_∷ ([ ρ ] A₁)) (trans ceq (sym pΓ)))
                      (subst (λ z → Q ∣ _ <:̂ᵛ z) (sym pA) st)
                      (subst (λ z → Q ⊩ _ ≾̂ₑ z) (sym pt) le)

  -- subsumption
  --
  -- Invisible to erasure; its two witnesses compose with the slack.

  completeC Γ A t (subC D (p ‼ₛ q)) ceq st le =
    completeC Γ A t D ceq (<:̂ᵛ-trans p st) (transₑ q le)

-- Satisfying the generated constraint is equivalent to erasing from a
-- derivation, up to derivation choice.

charV : ∀ {Θ n Θ'} → (Γ : OCtx Θ n) → (V : RawV n) → (A : OVType Θ)
      → (σ : Subst Θ Θ') → (Q : Hyps Θ')
      ----------------------------------------------------------------
      → (σ ⊨[ Q ] genV Γ V A)
        ⇔ (Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢V⦂ A [ σ ]ᵛ) ] (⌊ D ⌋ᵛ ≡ V))

charV Γ V A σ Q =
  mk⇔ (soundV Γ V A)
      (λ { (D , e) → subst (λ W → σ ⊨[ Q ] genV Γ W A) e
                           (completeV Γ A D refl (<:̂ᵛ-refl (A [ σ ]ᵛ))) })

charC : ∀ {Θ n Θ'} → (Γ : OCtx Θ n) → (M : RawC n) → (A : OVType Θ)
      → (t : EExp Θ) → (σ : Subst Θ Θ') → (Q : Hyps Θ')
      ------------------------------------------------------------------------
      → (σ ⊨[ Q ] genC Γ M (A ‼ t))
        ⇔ (Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢C⦂ A [ σ ]ᵛ ‼ t [ σ ]ᵉ) ] (⌊ D ⌋ᶜ ≡ M))

charC Γ M A t σ Q =
  mk⇔ (soundC Γ M A t)
      (λ { (D , e) → subst (λ N → σ ⊨[ Q ] genC Γ N (A ‼ t)) e
                           (completeC Γ A t D refl (<:̂ᵛ-refl (A [ σ ]ᵛ))
                                      ⊩≾̂ₑ-refl) })

-- Sanity checks: completeness computes on examples.

private

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  -- a `return` with slack absorbed: the generated `≾̂ₑᶜ` is the hypothesis

  ex-return : idˢ ⊨[ ∅ᴴ ] genC (∅ᶜ ∷ Unit) (return ⋆) (Unit ‼ ûₑ)
  ex-return = completeC {σ = idˢ} (∅ᶜ ∷ Unit) Unit ûₑ (return ⋆) refl Unitₛ ⊩≾̂ₑ-refl

  -- a subsumption erases away, and completeness sees the same constraint

  ex-sub : idˢ ⊨[ ∅ᴴ ] genC (∅ᶜ ∷ Unit) (return ⋆) (Unit ‼ ûₑ)
  ex-sub = completeC {σ = idˢ} (∅ᶜ ∷ Unit) Unit ûₑ
                     (coerce ⊩≾̂ₑ-refl (return ⋆)) refl Unitₛ ⊩≾̂ₑ-refl

  -- a variable typed at a supertype: the atom is the subsumption's witness

  ex-var : idˢ ⊨[ ∅ᴴ ] genV (∅ᶜ ∷ [ ûᵣ ] Unit) (var zero) ([ ûᵣ ] Unit)
  ex-var = completeV {σ = idˢ} (∅ᶜ ∷ [ ûᵣ ] Unit) ([ ûᵣ ] Unit)
                     (subV (var Hd (≾ᵘ-ok ⊩≾̂ᵣ-refl)) (<:̂ᵛ-refl ([ ûᵣ ] Unit)))
                     refl (<:̂ᵛ-refl ([ ûᵣ ] Unit))

  -- unboxing a boxed variable: the gate is `false`, the row is inhabited

  ex-unbox : idˢ ⊨[ ∅ᴴ ] genC (∅ᶜ ∷ [ ûᵣ ] Unit) (unbox zero (return ⋆))
                              (Unit ‼ ûₑ)
  ex-unbox = completeC {σ = idˢ} (∅ᶜ ∷ [ ûᵣ ] Unit) Unit ûₑ
                       (unbox Hd ⊩≾̂ᵣ-refl (<:̂ᵛ-refl Unit) (return ⋆))
                       refl Unitₛ ⊩≾̂ₑ-refl
