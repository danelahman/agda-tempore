------------------------------------------------------------------
-- Completeness of constraint generation                          --
--                                                                --
-- Every mirrored derivation solves the constraint generated from --
-- its own erasure:                                               --
--                                                                --
--   (D : Q ∣ Γ [ σ ]ᶜᵗˣ ⊢C⦂ A [ σ ]ᵛ ‼ ε) → Q ⊩ ε ≾̂ₑ t [ σ ]ᵉ    --
--     → σ ⊨[ Q ] genC Γ ⌊ D ⌋ᶜ (A ‼ t)                           --
--                                                                --
-- The proof is a structural induction on `D`, one case per       --
-- former. The context and the value type of `D` are *generalised*--
-- and related to the generation arguments by equations           --
-- (`Γ₀ ≡ Γ [ σ ]ᶜᵗˣ`, `A₀ ≡ A [ σ ]ᵛ`): a transported derivation --
-- is not a structural subterm, so the transports of              --
-- `Inference.Soundness` are replaced by hypotheses carried along --
-- the induction.                                                 --
--                                                                --
-- The effect of `D` is related to the expected effect by the     --
-- *slack* hypothesis `Q ⊩ ε ≾̂ₑ t [ σ ]ᵉ`, which is what makes    --
-- the `coerce` case go through (entailment transitivity). At     --
-- every recursive call the slack is reflexivity: generation's    --
-- inner expected effects are the `∃`-witnesses supplied here,    --
-- which are `D`'s own effects.                                   --
--                                                                --
-- The `∃`-witnesses are read off `D`; each generated fresh       --
-- variable instantiates to its witness *definitionally*          --
-- (`newᵗ`/`newʳ`/`newᵉ` are `zero`), so only the collapses of    --
-- the weakened generation arguments (`co*`, from                 --
-- `Inference.Soundness`, read right-to-left) remain.             --
------------------------------------------------------------------

-- `Bool` is renamed, as `OVType` has a constructor of that name
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Fin using (zero)
open import Data.Product using (Σ-syntax; _,_)

open import Function.Bundles using (_⇔_; mk⇔)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import Inference.Scopes

module Inference.Completeness (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Inference.Open.Grades         S
open import Inference.Open.Types          S
open import Inference.Open.Contexts       S
open import Inference.Open.ContextsLemmas S
open import Inference.Open.Subst          S
open import Inference.Open.Hyps           S
open import Inference.Open.Language       S

open import Inference.Raw.Syntax S
open import Inference.Erase      S

open import Inference.Constraints.Syntax       S
open import Inference.Constraints.Satisfaction S

open import Inference.Generate  S
open import Inference.Soundness S

--------------------------------------------------------------
-- Reading the two barrier-sensitive rows backwards          --
--                                                           --
-- `VarC`/`UnboxC` dispatch on the same flag as               --
-- `VarOK`/`UnboxOK`, so the premise of the mirrored rule     --
-- *is* the satisfaction of the generated row.                --
--------------------------------------------------------------

VarOK-VarC : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (Q : Hyps Θ')
           → (A : OVType Θ) → (ρ : RExp Θ) → (b : 𝔹)
           → VarOK Q (A [ σ ]ᵛ) (ρ [ σ ]ʳ) b
           --------------------------------
           → σ ⊨[ Q ] VarC A ρ b

VarOK-VarC σ Q A ρ true  ok = ok
VarOK-VarC σ Q A ρ false ok = ok

-- A derivable unboxing is a non-crossing one, and its row is then the
-- guarded constraint itself; the crossing case is `⊥`.

UnboxOK-UnboxC : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {C : Constraint Θ}
                 {ρ' ρ : RExp Θ'}
               → (b : 𝔹)
               → UnboxOK Q ρ' ρ b
               → (Q ⊩ ρ' ≾̂ᵣ ρ → σ ⊨[ Q ] C)
               ----------------------------
               → σ ⊨[ Q ] UnboxC C b

UnboxOK-UnboxC false ok f = f ok

--------------------------------------------------------------
-- The theorem                                               --
--------------------------------------------------------------

mutual

  completeV : ∀ {Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {Γ₀ : OCtx Θ' n}
            → (Γ : OCtx Θ n) → (A : OVType Θ)
            → {A₀ : OVType Θ'}
            → (D : Q ∣ Γ₀ ⊢V⦂ A₀)
            → Γ₀ ≡ Γ [ σ ]ᶜᵗˣ
            → A₀ ≡ A [ σ ]ᵛ
            --------------------------
            → σ ⊨[ Q ] genV Γ ⌊ D ⌋ᵛ A

  -- variables
  --
  -- The raw index is `var-pos x`, at which the three lookups agree with
  -- the type, the grade and the crossing flag of `x` itself.

  completeV {σ = σ} {Q = Q} Γ A (var {A = A₁} {ρ = ρ₁} x ok) ceq aeq =
    trans lty aeq ,
    VarOK-VarC σ Q (lookup-ty Γ i) (lookup-gr Γ i) (lookup-crosses Γ i) ok'
    where
      i = var-pos x

      lty : lookup-ty Γ i [ σ ]ᵛ ≡ A₁
      lty = trans (sym (lookup-ty-subst Γ σ i))
                  (trans (cong (λ G → lookup-ty G i) (sym ceq)) (var-pos-ty x))

      lgr : lookup-gr Γ i [ σ ]ʳ ≡ ρ₁
      lgr = trans (sym (lookup-gr-subst Γ σ i))
                  (trans (cong (λ G → lookup-gr G i) (sym ceq)) (var-pos-gr x))

      flg : lookup-crosses Γ i ≡ crossesᴱ̂ x
      flg = trans (sym (lookup-crosses-subst Γ σ i))
                  (trans (cong (λ G → lookup-crosses G i) (sym ceq))
                         (lookup-crosses-var x))

      ok' : VarOK Q (lookup-ty Γ i [ σ ]ᵛ) (lookup-gr Γ i [ σ ]ʳ)
                    (lookup-crosses Γ i)
      ok' = subst (VarOK Q (lookup-ty Γ i [ σ ]ᵛ) (lookup-gr Γ i [ σ ]ʳ))
                  (sym flg)
                  (subst₂ (λ A₂ ρ₂ → VarOK Q A₂ ρ₂ (crossesᴱ̂ x))
                          (sym lty) (sym lgr) ok)

  -- base-typed constants, unit, booleans

  completeV Γ A (const B c) ceq aeq = aeq
  completeV Γ A ⋆           ceq aeq = aeq
  completeV Γ A true        ceq aeq = aeq
  completeV Γ A false       ceq aeq = aeq

  -- pairing

  completeV {Θ = Θ} {σ = σ} Γ A (⦉_,_⦊ {A = A₁} {B = A₂} D₁ D₂) ceq aeq =
    A₁ , A₂ , trans aeq (sym pA) , ih₁ , ih₂
    where
      Γ↑ = wkᵗ-ctx (wkᵗ-ctx Γ)
      α₁ = wkᵗ-v (tvar (newᵗ {Θ}))
      α₂ = tvar (newᵗ {Θ +ty})

      pΓ = co²ᵗ-ctx σ A₁ A₂ Γ
      pA = co²ᵗ-v   σ A₁ A₂ A

      ih₁ = completeV Γ↑ α₁ D₁ (trans ceq (sym pΓ)) refl
      ih₂ = completeV Γ↑ α₂ D₂ (trans ceq (sym pΓ)) refl

  -- lambda abstraction

  completeV {Θ = Θ} {σ = σ} Γ A
            (lam {A = A₁} {C = A₂ ‼ ε₀} D) ceq aeq =
    A₁ , A₂ , ε₀ , trans aeq (sym pA) , ih
    where
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx (wkᵗ-ctx Γ))
      α₁ = wkᵉ-v (wkᵗ-v (tvar (newᵗ {Θ})))
      α₂ = wkᵉ-v (tvar (newᵗ {Θ +ty}))
      e  = evar (newᵉ {Θ +ty +ty})

      pΓ = co²ᵗᵉ-ctx σ A₁ A₂ ε₀ Γ
      pA = co²ᵗᵉ-v   σ A₁ A₂ ε₀ A

      ih = completeC (Γ↑ ∷ α₁) α₂ e D
                     (cong (_∷ A₁) (trans ceq (sym pΓ))) refl ⊩≾̂ₑ-refl


  completeC : ∀ {Θ n Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {Γ₀ : OCtx Θ' n}
            → (Γ : OCtx Θ n) → (A : OVType Θ) → (t : EExp Θ)
            → {A₀ : OVType Θ'} → {ε₀ : EExp Θ'}
            → (D : Q ∣ Γ₀ ⊢C⦂ A₀ ‼ ε₀)
            → Γ₀ ≡ Γ [ σ ]ᶜᵗˣ
            → A₀ ≡ A [ σ ]ᵛ
            → Q ⊩ ε₀ ≾̂ₑ t [ σ ]ᵉ
            --------------------------------
            → σ ⊨[ Q ] genC Γ ⌊ D ⌋ᶜ (A ‼ t)

  -- returning a value

  completeC Γ A t (return D) ceq aeq le = completeV Γ A D ceq aeq , le

  -- sequential composition
  --
  -- The witnesses make the continuation's context an instance of the
  -- generated one on the nose: `∣ e₁ ∣̂ᵉ` instantiates to `∣ ε₁ ∣̂ᵉ`.

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t
            (_⨟_ {A = A₁} {ε' = ε₂} {ε = ε₁} D₁ D₂) ceq aeq le =
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

      ih₁ = completeC Γ↑ α e₁ D₁ (trans ceq (sym pΓ)) refl ⊩≾̂ₑ-refl
      ih₂ = completeC (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) A↑ e₂ D₂
                      (cong (λ G → G ⟨ ∣ ε₁ ∣̂ᵉ ⟩ ∷ A₁) (trans ceq (sym pΓ)))
                      (trans aeq (sym pA)) ⊩≾̂ₑ-refl

  -- function application

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t
            (_·_ {A = A₁} {C = A₀ ‼ ε₀} D₁ D₂) ceq aeq le =
    A₁ , ε₀ , ih₁ , ih₂ , subst (λ z → Q ⊩ ε₀ ≾̂ₑ z) (sym pt) le
    where
      Γ↑ = wkᵉ-ctx (wkᵗ-ctx Γ)
      A↑ = wkᵉ-v (wkᵗ-v A)
      α  = wkᵉ-v (tvar (newᵗ {Θ}))
      e  = evar (newᵉ {Θ +ty})

      pΓ = coᵗᵉ-ctx σ A₁ ε₀ Γ
      pA = coᵗᵉ-v   σ A₁ ε₀ A
      pt = coᵗᵉ-e   σ A₁ ε₀ t

      ih₁ = completeV Γ↑ (α ⇒ (A↑ ‼ e)) D₁ (trans ceq (sym pΓ))
                      (cong (λ Z → A₁ ⇒ (Z ‼ ε₀)) (trans aeq (sym pA)))
      ih₂ = completeV Γ↑ α D₂ (trans ceq (sym pΓ)) refl

  -- pattern-matching

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t
            (match_`in_ {A = A₁} {B = A₂} D₁ D₂) ceq aeq le =
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

      ih₁ = completeV Γ↑ (α₁ |×| α₂) D₁ (trans ceq (sym pΓ)) refl
      ih₂ = completeC (Γ↑ ∷ α₁ ∷ α₂) A↑ t↑ D₂
                      (cong (λ G → G ∷ A₁ ∷ A₂) (trans ceq (sym pΓ)))
                      (trans aeq (sym pA))
                      (subst (λ z → Q ⊩ _ ≾̂ₑ z) (sym pt) le)

  -- empty type elimination

  completeC Γ A t (absurd D) ceq aeq le = completeV Γ Empty D ceq refl

  -- boolean elimination

  completeC Γ A t (if_`then_`else_ D₀ D₁ D₂) ceq aeq le =
    completeV Γ Bool D₀ ceq refl ,
    completeC Γ A t D₁ ceq aeq le ,
    completeC Γ A t D₂ ceq aeq le

  -- performing algebraic operations

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t
            (perform {ε = ε} op D₁ D₂) ceq aeq le =
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
                      (sym (⌜⌝ᵍ-subst σ' (param op)))
      ih₂ = completeC (Γ↑ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ) A↑ e D₂
                      (cong₂ (λ G Z → G ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ Z)
                             (trans ceq (sym pΓ))
                             (sym (⌜⌝ᵍ-subst σ' (arity op))))
                      (trans aeq (sym pA)) ⊩≾̂ₑ-refl

  -- explicit delaying of a computation

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t (delay {ε = ε} τ D) ceq aeq le =
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
                     (trans aeq (sym pA)) ⊩≾̂ₑ-refl

  -- effect handling
  --
  -- The clause family is handled pointwise, one `∀ᵉ` deeper: the rigid
  -- effect-grade variable of generation instantiates to the rigid variable
  -- of the rule definitionally, so the clause's slack is reflexivity and
  -- only the clause context's weakenings and the two ground-type
  -- embeddings have to be collapsed.

  completeC {Θ = Θ} {Θ' = Θ'} {σ = σ} {Q = Q} Γ A t
            (handle_`with_`in {A = A₁} {ε = ε₁} {ε' = ε₂} D₁ H D₂) ceq aeq le =
    A₁ , ε₁ , ε₂ , ih₁ , ih₂ ,
    subst (λ z → Q ⊩ ε₁ ·̂ₑ ε₂ ≾̂ₑ z) (sym pt) le , ihH
    where
      σ'  = σ ,ᵗ A₁ ,ᵉ ε₁ ,ᵉ ε₂
      Γ↑  = wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx Γ))
      A↑  = wkᵉ-v (wkᵉ-v (wkᵗ-v A))
      α   = wkᵉ-v (wkᵉ-v (tvar (newᵗ {Θ})))
      e₁  = wkᵉ-e (evar (newᵉ {Θ +ty}))
      e₂  = evar (newᵉ {Θ +ty +e})
      Γ⇑  = wkᵉ-ctx (wkᵉ-ctx (wkᵉ-ctx (wkᵗ-ctx Γ)))
      A⇑  = wkᵉ-v (wkᵉ-v (wkᵉ-v (wkᵗ-v A)))
      e'' = evar (newᵉ {Θ +ty +e +e})

      pΓ  = coᵗ²ᵉ-ctx  σ A₁ ε₁ ε₂ Γ
      pA  = coᵗ²ᵉ-v    σ A₁ ε₁ ε₂ A
      pt  = coᵗ²ᵉ-e    σ A₁ ε₁ ε₂ t
      pΓ⇑ = coᵗ²ᵉ-ctx↑ σ A₁ ε₁ ε₂ Γ
      pA⇑ = coᵗ²ᵉ-v↑   σ A₁ ε₁ ε₂ A

      ih₁ = completeC Γ↑ α e₁ D₁ (trans ceq (sym pΓ)) refl ⊩≾̂ₑ-refl
      ih₂ = completeC (Γ↑ ⟨ ∣ e₁ ∣̂ᵉ ⟩ ∷ α) A↑ e₂ D₂
                      (cong (λ G → G ⟨ ∣ ε₁ ∣̂ᵉ ⟩ ∷ A₁) (trans ceq (sym pΓ)))
                      (trans aeq (sym pA)) ⊩≾̂ₑ-refl

      aH : wkᵉ-v _ ≡ A⇑ [ σ' ↑ᵉ ]ᵛ
      aH = trans (cong wkᵉ-v aeq) (sym pA⇑)

      cH : (op : Op)
         → (wkᵉ-ctx _) ᴱ̂ ∷ ⌜ param op ⌝ᵍ
              ∷ [ rconst (mapᵉ (op-grade op)) ]
                  (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v _ ‼ evar (newᵉ {Θ'}))
           ≡ (Γ⇑ ᴱ̂ ∷ ⌜ param op ⌝ᵍ
                ∷ [ rconst (mapᵉ (op-grade op)) ] (⌜ arity op ⌝ᵍ ⇒ A⇑ ‼ e''))
             [ σ' ↑ᵉ ]ᶜᵗˣ
      cH op =
        cong₂ _∷_
              (cong₂ _∷_ (cong _ᴱ̂ (trans (cong wkᵉ-ctx ceq) (sym pΓ⇑)))
                         (sym (⌜⌝ᵍ-subst (σ' ↑ᵉ) (param op))))
              (cong₂ (λ X Y → [ rconst (mapᵉ (op-grade op)) ]
                                (X ⇒ Y ‼ evar (newᵉ {Θ'})))
                     (sym (⌜⌝ᵍ-subst (σ' ↑ᵉ) (arity op)))
                     aH)

      ihH : (op : Op) → _
      ihH op =
        completeC (Γ⇑ ᴱ̂ ∷ ⌜ param op ⌝ᵍ
                      ∷ [ rconst (mapᵉ (op-grade op)) ] (⌜ arity op ⌝ᵍ ⇒ A⇑ ‼ e''))
                  A⇑ (econst (op-grade op) ·̂ₑ e'')
                  (H op) (cH op) aH ⊩≾̂ₑ-refl

  -- unboxing a boxed variable
  --
  -- The gate is `lookup-crosses Γ (var-pos x)`, which the alignment `flg`
  -- rewrites to the witness's own flag; a derivable `unbox` has that flag
  -- `false` (`UnboxOK … true = ⊥`), and the guarded row is then the row.

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t
            (unbox {A = A₁} {ρ = ρ₁} {ρ' = ρ'} x ok D) ceq aeq le =
    subst (λ b → σ ⊨[ Q ] UnboxC Cᵘ b) (sym flg)
          (UnboxOK-UnboxC (crossesᴱ̂ x) ok row)
    where
      i  = var-pos x
      σ' = σ ,ᵗ A₁ ,ʳ ρ₁
      Γ↑ = wkʳ-ctx (wkᵗ-ctx Γ)
      A↑ = wkʳ-v (wkᵗ-v A)
      t↑ = wkʳ-e (wkᵗ-e t)
      α  = wkʳ-v (tvar (newᵗ {Θ}))
      r  = rvar (newʳ {Θ +ty})

      Cᵘ = ∃ᵗ (∃ʳ (  (lookup-ty Γ↑ i ≐ᵥ [ r ] α)
                   ∧̂ (lookup-gr Γ↑ i ≾̂ᵣᶜ r)
                   ∧̂ genC (Γ↑ ∷ α) ⌊ D ⌋ᶜ (A↑ ‼ t↑)))

      pΓ = coᵗʳ-ctx σ A₁ ρ₁ Γ
      pA = coᵗʳ-v   σ A₁ ρ₁ A
      pt = coᵗʳ-e   σ A₁ ρ₁ t

      flg : lookup-crosses Γ i ≡ crossesᴱ̂ x
      flg = trans (sym (lookup-crosses-subst Γ σ i))
                  (trans (cong (λ G → lookup-crosses G i) (sym ceq))
                         (lookup-crosses-var x))

      -- lookup in the weakened context, instantiated, is lookup in `Γ₀`

      lty : lookup-ty Γ↑ i [ σ' ]ᵛ ≡ [ ρ₁ ] A₁
      lty = trans (cong (_[ σ' ]ᵛ)
                        (trans (lookup-ty-wkʳ (wkᵗ-ctx Γ) i)
                               (cong wkʳ-v (lookup-ty-wkᵗ Γ i))))
            (trans (coᵗʳ-v σ A₁ ρ₁ (lookup-ty Γ i))
            (trans (sym (lookup-ty-subst Γ σ i))
            (trans (cong (λ G → lookup-ty G i) (sym ceq)) (var-pos-ty x))))

      lgr : lookup-gr Γ↑ i [ σ' ]ʳ ≡ ρ'
      lgr = trans (cong (_[ σ' ]ʳ)
                        (trans (lookup-gr-wkʳ (wkᵗ-ctx Γ) i)
                               (cong wkʳ-r (lookup-gr-wkᵗ Γ i))))
            (trans (coᵗʳ-r σ A₁ ρ₁ (lookup-gr Γ i))
            (trans (sym (lookup-gr-subst Γ σ i))
            (trans (cong (λ G → lookup-gr G i) (sym ceq)) (var-pos-gr x))))

      row : Q ⊩ ρ' ≾̂ᵣ ρ₁ → σ ⊨[ Q ] Cᵘ
      row ok' =
        A₁ , ρ₁ , lty , subst (λ z → Q ⊩ z ≾̂ᵣ ρ₁) (sym lgr) ok' ,
        completeC (Γ↑ ∷ α) A↑ t↑ D
                  (cong (_∷ A₁) (trans ceq (sym pΓ)))
                  (trans aeq (sym pA))
                  (subst (λ z → Q ⊩ _ ≾̂ₑ z) (sym pt) le)

  -- boxing up a value

  completeC {Θ = Θ} {σ = σ} {Q = Q} Γ A t (box {A = A₁} ρ D₁ D₂) ceq aeq le =
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
                      (cong (_⟨ ρ ⟩) (trans ceq (sym pΓ))) refl
      ih₂ = completeC (Γ↑ ∷ [ r ] α) A↑ t↑ D₂
                      (cong (_∷ ([ ρ ] A₁)) (trans ceq (sym pΓ)))
                      (trans aeq (sym pA))
                      (subst (λ z → Q ⊩ _ ≾̂ₑ z) (sym pt) le)

  -- (shallow explicit) sub-effecting
  --
  -- The one case the slack hypothesis exists for: `coerce` is invisible to
  -- erasure, and its entailment composes with the slack.

  completeC Γ A t (coerce p D) ceq aeq le =
    completeC Γ A t D ceq aeq (transₑ p le)

--------------------------------------------------------------
-- Characterisation                                          --
--                                                           --
-- Satisfaction of a generated constraint and existence of a  --
-- derivation erasing to the raw term are equivalent, up to   --
-- existence (mirrored derivations are proof-relevant).       --
--------------------------------------------------------------

charV : ∀ {Θ n Θ'} → (Γ : OCtx Θ n) → (V : RawV n) → (A : OVType Θ)
      → (σ : Subst Θ Θ') → (Q : Hyps Θ')
      ----------------------------------------------------------------
      → (σ ⊨[ Q ] genV Γ V A)
        ⇔ (Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢V⦂ A [ σ ]ᵛ) ] (⌊ D ⌋ᵛ ≡ V))

charV Γ V A σ Q =
  mk⇔ (soundV Γ V A)
      (λ { (D , e) → subst (λ W → σ ⊨[ Q ] genV Γ W A) e
                           (completeV Γ A D refl refl) })

charC : ∀ {Θ n Θ'} → (Γ : OCtx Θ n) → (M : RawC n) → (A : OVType Θ)
      → (t : EExp Θ) → (σ : Subst Θ Θ') → (Q : Hyps Θ')
      ------------------------------------------------------------------------
      → (σ ⊨[ Q ] genC Γ M (A ‼ t))
        ⇔ (Σ[ D ∈ (Q ∣ Γ [ σ ]ᶜᵗˣ ⊢C⦂ A [ σ ]ᵛ ‼ t [ σ ]ᵉ) ] (⌊ D ⌋ᶜ ≡ M))

charC Γ M A t σ Q =
  mk⇔ (soundC Γ M A t)
      (λ { (D , e) → subst (λ N → σ ⊨[ Q ] genC Γ N (A ‼ t)) e
                           (completeC Γ A t D refl refl ⊩≾̂ₑ-refl) })

--------------------------------------------------------------
-- Sanity checks: completeness computes                      --
--------------------------------------------------------------

private

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  -- a `return` with slack absorbed: the generated `≾̂ₑᶜ` is the hypothesis

  ex-return : idˢ ⊨[ ∅ᴴ ] genC (∅ᶜ ∷ Unit) (return ⋆) (Unit ‼ ûₑ)
  ex-return = completeC {σ = idˢ} (∅ᶜ ∷ Unit) Unit ûₑ (return ⋆) refl refl ⊩≾̂ₑ-refl

  -- a `coerce` erases away, and completeness sees the same constraint

  ex-coerce : idˢ ⊨[ ∅ᴴ ] genC (∅ᶜ ∷ Unit) (return ⋆) (Unit ‼ ûₑ)
  ex-coerce = completeC {σ = idˢ} (∅ᶜ ∷ Unit) Unit ûₑ
                        (coerce ⊩≾̂ₑ-refl (return ⋆)) refl refl ⊩≾̂ₑ-refl

  -- unboxing a boxed variable: the gate is `false`, the row is inhabited

  ex-unbox : idˢ ⊨[ ∅ᴴ ] genC (∅ᶜ ∷ [ ûᵣ ] Unit) (unbox zero (return ⋆))
                              (Unit ‼ ûₑ)
  ex-unbox = completeC {σ = idˢ} (∅ᶜ ∷ [ ûᵣ ] Unit) Unit ûₑ
                       (unbox Hd ⊩≾̂ᵣ-refl (return ⋆)) refl refl ⊩≾̂ₑ-refl
