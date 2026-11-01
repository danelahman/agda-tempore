------------------------------------------------------------------------
-- The bisimulation, rule by rule.
------------------------------------------------------------------------

open import Data.Product

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Relation.Nullary using (¬_)

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.StateEquivalence.Bisimulation (Spec : LanguageSpec) where
open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec

open import MonomorphicCalculus.Syntax.Contexts        Spec
open import MonomorphicCalculus.Syntax.Terms           Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming        Spec
open import MonomorphicCalculus.Syntax.Substitution    Spec
open import MonomorphicCalculus.Syntax.Types           Spec

open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Renaming.Coherence    Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence     Spec
open import MonomorphicCalculus.Syntax.Terms.Transport       Spec
open import MonomorphicCalculus.Syntax.Substitution.Variables  Spec
open import MonomorphicCalculus.OperationalSemantics.GradedReach Spec
open import MonomorphicCalculus.Syntax.Substitution.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Substitution.Subsumption  Spec

open import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Core Spec
open import MonomorphicCalculus.OperationalSemantics.StateEquivalence.Extensions Spec

-- `Sim es M' r` is what simulating `r` from the related configuration
-- amounts to: a state, a reduct, their relations, the step, and the fact
-- that the two steps extend the state alike.

Sim : ∀ {A A₁ ε ε₁} {𝕊 𝕊' 𝕊₁ : State []}
    → (es : 𝕊 ≐ˢ 𝕊') → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → (M' : toCtx 𝕊' ⊢ᶜ⦂ A ! ε)
    → {N : toCtx 𝕊₁ ⊢ᶜ⦂ A₁ ! ε₁} → (r : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊₁ ∣ N ⟩) → Set
Sim {A₁ = A₁} {ε₁ = ε₁} {𝕊' = 𝕊'} {𝕊₁ = 𝕊₁} es M' {N} r =
  Σ[ 𝕊₁' ∈ State [] ] Σ[ N' ∈ (toCtx 𝕊₁' ⊢ᶜ⦂ A₁ ! ε₁) ] Σ[ es₁ ∈ 𝕊₁ ≐ˢ 𝕊₁' ]
  Σ[ r' ∈ (⟨ 𝕊' ∣ M' ⟩ ⟶ ⟨ 𝕊₁' ∣ N' ⟩) ]
    (step-extends-state r ≤≐ step-extends-state r')
  × (N ≡ castᶜ (sym (toCtx-≐ˢ es₁)) N')

-- subsumption at a computation: the coercion is discarded on both sides, the
-- reduct being the coerced computation itself.

⟶-≐ˢ-sub : ∀ {A A' ε ε'} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
        → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → {w : (A ! ε) <:ᶜ (A' ! ε')}
        → (P' : toCtx 𝕊' ⊢ᶜ⦂ A' ! ε')
        → subC M w ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
        → Sim es P' (SUB {M = M} {w = w})
⟶-≐ˢ-sub es P' eM with cast-sub⁻ (sym (toCtx-≐ˢ es)) P' eM
... | w₁ , M₀' , refl , eM₀ = _ , _ , es , SUB , id-≤≐ , eM₀

-- subsumption at an eliminated function: the coercion splits the same way on
-- both sides.

⟶-≐ˢ-sub-app : ∀ {A A₁ B B₁ ε ε₁} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
            → {V : toCtx 𝕊 ⊢ᵛ⦂ A₁ ⇒ (B₁ ! ε₁)} → {W : toCtx 𝕊 ⊢ᵛ⦂ A}
            → {q : A <:ᵛ A₁} → {r : (B₁ ! ε₁) <:ᶜ B ! ε}
            → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε)
            → (subV V (q ⇒ₛ r) · W) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
            → Sim es P' (SUB-APP {V = V} {W = W} {q = q} {r = r})
⟶-≐ˢ-sub-app es {q = q} {r = r} P' eM
  with cast-app⁻ (sym (toCtx-≐ˢ es)) P' eM
... | Vf' , W' , refl , eVf , eW
  with cast-subV⁻ (sym (toCtx-≐ˢ es)) Vf' eVf
...   | q₁ ⇒ₛ r₁ , V' , refl , eV =
    _ , _ , es , SUB-APP , id-≤≐
  , trans (cong₂ _·_ eV (cong₂ subV eW (<:ᵛ-irrelevant q q₁)))
          (sym (trans (cast-app (sym (toCtx-≐ˢ es)))
                      (cong (_ ·_) (cast-subV (sym (toCtx-≐ˢ es))))))

-- subsumption at a handler literal: the coercion moves into the return
-- clause the same way on both sides.

cast-sub-handle : ∀ {Γ Γ' A A₁ B₁ ε ε₁ ε₁'} → (e : Γ' ≡ Γ)
                → {p : A <:ᵛ A₁} → {pε : ε ≾ₑ ε₁}
                → (M' : Γ' ⊢ᶜ⦂ A ! ε)
                → (N' : Γ' ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A₁ ⊢ᶜ⦂ B₁ ! ε₁')
                → (H' : (op : Op) → (ε₃ : E) →
                          Γ' ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                            ∷ [ ∣ op-grade op ∣ᵉ ]
                                (⌜ arity op ⌝ᵍ ⇒ B₁ ! ε₃)
                          ⊢ᶜ⦂ B₁ ! (op-grade op ·ₑ ε₃))
                → handle (castᶜ e M')
                  `with handler
                          (subCtx p
                            (C-rename (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ pε)))
                              (castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A₁) e) N')))
                          (λ op ε₃ →
                             castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                                                   ∷ [ ∣ op-grade op ∣ᵉ ]
                                                       (⌜ arity op ⌝ᵍ
                                                          ⇒ B₁ ! ε₃))
                                         e)
                                   (H' op ε₃))
                ≡ castᶜ e
                    (handle M'
                     `with handler
                             (subCtx p
                               (C-rename (cong-∷-ren (⟨⟩-≤-ren (map-monotoneᵉ pε))) N'))
                             H')
cast-sub-handle refl M' N' H' = refl

⟶-≐ˢ-sub-handle : ∀ {A A₁ B B₁ ε ε₁ ε' ε₁'} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
               → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
               → {N : toCtx 𝕊 ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A₁ ⊢ᶜ⦂ B₁ ! ε₁'}
               → {H : (op : Op) → (ε₃ : E) →
                        toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                          ∷ [ ∣ op-grade op ∣ᵉ ]
                              (⌜ arity op ⌝ᵍ ⇒ B₁ ! ε₃)
                        ⊢ᶜ⦂ B₁ ! (op-grade op ·ₑ ε₃)}
               → {p : A <:ᵛ A₁} → {pε : ε ≾ₑ ε₁}
               → {q : (B₁ ! ε₁') <:ᶜ (B ! ε')}
               → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! (ε ·ₑ ε'))
               → (handle M `with subV (handler N H) ((p !ₛ pε) ⇛ₛ q))
                   ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
               → Sim es P' (SUB-HANDLE {M = M} {N = N} {H = H} {p = p} {pε = pε} {q = q})
⟶-≐ˢ-sub-handle es P' eM with cast-handle⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M' , W' , refl , eM₁ , eW with cast-subV-at⁻ (sym (toCtx-≐ˢ es)) W' eW
...   | V' , refl , eV with cast-handler⁻ (sym (toCtx-≐ˢ es)) V' eV
...     | H' , N' , refl , eH , eN =
    _ , _ , es , SUB-HANDLE , id-≤≐
  , trans (cong₂ handle_`with_ eM₁
             (handler-≡ (cong (subCtx _) (C-rename-cong (cong-∷-ren _) eN)) eH))
          (cast-sub-handle (sym (toCtx-≐ˢ es)) M' N' H')

-- nested subsumption at a handler: the coercions compose on both sides.

⟶-≐ˢ-sub-handle-trans : ∀ {A₀ A' A B ε ε'} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
                     → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → {V : toCtx 𝕊 ⊢ᵛ⦂ A₀}
                     → {p : A₀ <:ᵛ A'} → {p' : A' <:ᵛ (A ! ε) ⇛ (B ! ε')}
                     → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! (ε ·ₑ ε'))
                     → (handle M `with subV (subV V p) p')
                         ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
                     → Sim es P' (SUB-HANDLE-TRANS {M = M} {V = V} {p = p} {p' = p'})
⟶-≐ˢ-sub-handle-trans es P' eM with cast-handle⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M' , W' , refl , eM₁ , eW with cast-subV-at⁻ (sym (toCtx-≐ˢ es)) W' eW
...   | W₁' , refl , eW₁ with cast-subV-at⁻ (sym (toCtx-≐ˢ es)) W₁' eW₁
...     | V' , refl , eV =
    _ , _ , es , SUB-HANDLE-TRANS , id-≤≐
  , trans (cong₂ handle_`with_ eM₁ (cong (λ v → subV v _) eV))
          (sym (trans (cast-handle (sym (toCtx-≐ˢ es)))
                      (cong (handle _ `with_) (cast-subV (sym (toCtx-≐ˢ es))))))

-- subsumption at a scrutinised boolean: `boolₛ` is dropped on both sides.

⟶-≐ˢ-sub-if : ∀ {A ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
           → {V : toCtx 𝕊 ⊢ᵛ⦂ bool} → {M N : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
           → (P' : toCtx 𝕊' ⊢ᶜ⦂ A ! ε)
           → (if subV V boolₛ `then M `else N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
           → Sim es P' (SUB-IF {V = V} {M = M} {N = N})
⟶-≐ˢ-sub-if es P' eM with cast-if⁻ (sym (toCtx-≐ˢ es)) P' eM
... | Vb' , M₀' , N₀' , refl , eVb , eM₀ , eN₀
  with cast-subV⁻ (sym (toCtx-≐ˢ es)) Vb' eVb
...   | boolₛ , V' , refl , eV =
    _ , _ , es , SUB-IF , id-≤≐
  , trans (cong₃ (λ v m n → if v `then m `else n) eV eM₀ eN₀)
          (sym (cast-if (sym (toCtx-≐ˢ es))))

-- subsumption at a scrutinised natural number: `natₛ` is dropped on both
-- sides.

⟶-≐ˢ-sub-matchℕ : ∀ {A ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
              → {V : toCtx 𝕊 ⊢ᵛ⦂ nat} → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
              → {N : toCtx 𝕊 ∷ nat ⊢ᶜ⦂ A ! ε}
              → (P' : toCtx 𝕊' ⊢ᶜ⦂ A ! ε)
              → (matchℕ subV V natₛ `zero M `succ N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
              → Sim es P' (SUB-MATCHℕ {V = V} {M = M} {N = N})
⟶-≐ˢ-sub-matchℕ es P' eM with cast-matchℕ⁻ (sym (toCtx-≐ˢ es)) P' eM
... | Vn' , M₀' , N₀' , refl , eVn , eM₀ , eN₀
  with cast-subV⁻ (sym (toCtx-≐ˢ es)) Vn' eVn
...   | natₛ , V' , refl , eV =
    _ , _ , es , SUB-MATCHℕ , id-≤≐
  , trans (cong₃ (λ v m n → matchℕ v `zero m `succ n) eV eM₀ eN₀)
          (sym (cast-matchℕ (sym (toCtx-≐ˢ es))))

-- subsumption at a recursion's natural number: `natₛ` is dropped on both
-- sides.

⟶-≐ˢ-sub-recℕ : ∀ {B ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
             → {V : toCtx 𝕊 ⊢ᵛ⦂ nat} → {M : toCtx 𝕊 ⊢ᶜ⦂ B ! ε}
             → {N : (toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
             → {p : ε ·ₑ ε ≾ₑ ε}
             → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε)
             → recℕ (subV V natₛ) M N p ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
             → Sim es P' (SUB-RECℕ {V = V} {M = M} {N = N} {p = p})
⟶-≐ˢ-sub-recℕ es {p = p} P' eM with cast-recℕ⁻ (sym (toCtx-≐ˢ es)) P' eM
... | Vn' , M₀' , N₀' , refl , eVn , eM₀ , eN₀
  with cast-subV⁻ (sym (toCtx-≐ˢ es)) Vn' eVn
...   | natₛ , V' , refl , eV =
    _ , _ , es , SUB-RECℕ , id-≤≐
  , trans (cong₃ (λ v m n → recℕ v m n p) eV eM₀ eN₀)
          (sym (cast-recℕ (sym (toCtx-≐ˢ es))))

-- boolean elimination: the scrutinee is the same constant on both sides
-- (`cast-true⁻`/`cast-false⁻`), and the reduct is the branch it names.

⟶-≐ˢ-if-true : ∀ {A ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
            → {M N : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
            → (P' : toCtx 𝕊' ⊢ᶜ⦂ A ! ε)
            → (if true `then M `else N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
            → Sim es P' (IF-TRUE {M = M} {N = N})
⟶-≐ˢ-if-true es P' eM with cast-if⁻ (sym (toCtx-≐ˢ es)) P' eM
... | V' , M₀' , N₀' , refl , eV , eM₀ , eN₀
      with cast-true⁻ (sym (toCtx-≐ˢ es)) V' eV
...     | refl = _ , _ , es , IF-TRUE , id-≤≐ , eM₀

⟶-≐ˢ-if-false : ∀ {A ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
             → {M N : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
             → (P' : toCtx 𝕊' ⊢ᶜ⦂ A ! ε)
             → (if false `then M `else N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
             → Sim es P' (IF-FALSE {M = M} {N = N})
⟶-≐ˢ-if-false es P' eM with cast-if⁻ (sym (toCtx-≐ˢ es)) P' eM
... | V' , M₀' , N₀' , refl , eV , eM₀ , eN₀
      with cast-false⁻ (sym (toCtx-≐ˢ es)) V' eV
...     | refl = _ , _ , es , IF-FALSE , id-≤≐ , eN₀

-- natural-number elimination: the scrutinee is `zero` on both sides
-- (`cast-zero⁻`), the reduct the zero branch; or the same successor
-- (`cast-succ⁻`), the reducts the same substitution into the successor branch.

⟶-≐ˢ-matchℕ-zero : ∀ {A ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
               → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → {N : toCtx 𝕊 ∷ nat ⊢ᶜ⦂ A ! ε}
               → (P' : toCtx 𝕊' ⊢ᶜ⦂ A ! ε)
               → (matchℕ zero `zero M `succ N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
               → Sim es P' (MATCHℕ-ZERO {M = M} {N = N})
⟶-≐ˢ-matchℕ-zero es P' eM with cast-matchℕ⁻ (sym (toCtx-≐ˢ es)) P' eM
... | V' , M₀' , N₀' , refl , eV , eM₀ , eN₀
      with cast-zero⁻ (sym (toCtx-≐ˢ es)) V' eV
...     | refl = _ , _ , es , MATCHℕ-ZERO , id-≤≐ , eM₀

⟶-≐ˢ-matchℕ-succ : ∀ {A ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
               → {V : toCtx 𝕊 ⊢ᵛ⦂ nat}
               → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → {N : toCtx 𝕊 ∷ nat ⊢ᶜ⦂ A ! ε}
               → (P' : toCtx 𝕊' ⊢ᶜ⦂ A ! ε)
               → (matchℕ succ V `zero M `succ N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
               → Sim es P' (MATCHℕ-SUCC {V = V} {M = M} {N = N})
⟶-≐ˢ-matchℕ-succ es P' eM with cast-matchℕ⁻ (sym (toCtx-≐ˢ es)) P' eM
... | U' , M' , N' , refl , eU , eM₀ , eN₀
      with cast-succ⁻ (sym (toCtx-≐ˢ es)) U' eU
...     | V' , refl , eV =
    _ , _ , es , MATCHℕ-SUCC , id-≤≐
  , subst (λ z → _ ≡ z) (cast-app-reduct (sym (toCtx-≐ˢ es)) N' V')
          (sub-≡ᶜ split-[] eV eN₀)

-- primitive recursion: the scrutinee is `zero` on both sides, the reduct the
-- base; or the same successor, the reducts the same unfolding.

⟶-≐ˢ-recℕ-zero : ∀ {B ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
              → {M : toCtx 𝕊 ⊢ᶜ⦂ B ! ε}
              → {N : (toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
              → {p : ε ·ₑ ε ≾ₑ ε}
              → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε)
              → recℕ zero M N p ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
              → Sim es P' (RECℕ-ZERO {M = M} {N = N} {p = p})
⟶-≐ˢ-recℕ-zero es P' eM with cast-recℕ⁻ (sym (toCtx-≐ˢ es)) P' eM
... | V' , M₀' , N₀' , refl , eV , eM₀ , eN₀
      with cast-zero⁻ (sym (toCtx-≐ˢ es)) V' eV
...     | refl = _ , _ , es , RECℕ-ZERO , id-≤≐ , eM₀

⟶-≐ˢ-recℕ-succ : ∀ {B ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
              → {V : toCtx 𝕊 ⊢ᵛ⦂ nat}
              → {M : toCtx 𝕊 ⊢ᶜ⦂ B ! ε}
              → {N : (toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ nat) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
              → {p : ε ·ₑ ε ≾ₑ ε}
              → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε)
              → recℕ (succ V) M N p ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
              → Sim es P' (RECℕ-SUCC {V = V} {M = M} {N = N} {p = p})
⟶-≐ˢ-recℕ-succ es {p = p} P' eM with cast-recℕ⁻ (sym (toCtx-≐ˢ es)) P' eM
... | U' , M' , N' , refl , eU , eM₀ , eN₀
      with cast-succ⁻ (sym (toCtx-≐ˢ es)) U' eU
...     | V' , refl , eV =
    _ , _ , es , RECℕ-SUCC , id-≤≐
  , trans (cong₃ (λ v m n → coerce p (recℕ v m n p ⨟ recℕ-step v n)) eV eM₀ eN₀)
          (cast-recℕ-reduct (sym (toCtx-≐ˢ es)) V' M' N' p)

-- application: the function is a lambda on both sides, and the reducts are the
-- same substitution (`sub-≡ᶜ`), the cast commuting with it (`cast-app-reduct`).

⟶-≐ˢ-app : ∀ {A B ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
        → {M₀ : toCtx 𝕊 ∷ A ⊢ᶜ⦂ B ! ε} → {V : toCtx 𝕊 ⊢ᵛ⦂ A}
        → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε)
        → (fun M₀ · V) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
        → Sim es P' (APP {M = M₀} {V = V})
⟶-≐ˢ-app es P' eM with cast-app⁻ (sym (toCtx-≐ˢ es)) P' eM
... | Vf' , W' , refl , eVf , eW with cast-fun⁻ (sym (toCtx-≐ˢ es)) Vf' eVf
...   | M₀' , refl , eM₀ =
    _ , _ , es , APP , id-≤≐
  , subst (λ z → _ ≡ z) (cast-app-reduct (sym (toCtx-≐ˢ es)) M₀' W')
          (sub-≡ᶜ split-[] eW eM₀)

-- a delay moves the lock into the state, so the two states are related by
-- `⟨⟩-≐ˢ` and the extensions by `⟨⟩-≤≐`

⟶-≐ˢ-delay : ∀ {A ε τ} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
          → {M₀ : toCtx 𝕊 ⟨ ιᵣ τ ⟩ ⊢ᶜ⦂ A ! ε}
          → (P' : toCtx 𝕊' ⊢ᶜ⦂ A ! (ιₑ τ ·ₑ ε))
          → delay τ M₀ ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
          → Sim es P' (DELAY {M = M₀})
⟶-≐ˢ-delay {τ = τ} es P' eM with cast-delay⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M₀' , refl , eM₀ =
    _ , _ , ⟨⟩-≐ˢ (ιᵣ τ) es , DELAY , ⟨⟩-≤≐ (ιᵣ τ) id-≤≐
  , subst (λ z → _ ≡ z) (castᶜ-irr _ _ M₀') eM₀

-- `box` allocates: the two states are related by `∷-≐ˢ` at the stored values
-- (`cast-box-val` moves the cast past the reindexing `_∷ₛ_` applies).

⟶-≐ˢ-box : ∀ {A B ρ ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
        → {V : toCtx 𝕊 ⟨ ρ ⟩ ⊢ᵛ⦂ A} → {M₀ : toCtx 𝕊 ∷ [ ρ ] A ⊢ᶜ⦂ B ! ε}
        → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε)
        → box _ V M₀ ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
        → Sim es P' (BOX {V = V} {M = M₀})
⟶-≐ˢ-box es P' eM with cast-box⁻ (sym (toCtx-≐ˢ es)) P' eM
... | V' , M₀' , refl , eV , eM₀ =
    _ , _
  , ∷-≐ˢ es (subst (λ z → _ ≡ z)
                   (cast-box-val (sym (toCtx-≐ˢ es)) V')
                   (V-rename-cong (eq-ren (sym ++ᶜ-identityˡ)) eV))
  , BOX , ∷-≤≐ id-≤≐
  , subst (λ z → _ ≡ z) (castᶜ-irr _ _ M₀') eM₀

-- list elimination: the scrutinee corresponds on both sides, and its
-- decomposition commutes with the cast (`listᵛ-cast`).

⟶-≐ˢ-matchL : ∀ {A D ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
            → {U : toCtx 𝕊 ⊢ᵛ⦂ list A}
            → {M₀ : toCtx 𝕊 ⊢ᶜ⦂ D ! ε} → {N₀ : toCtx 𝕊 ∷ A ∷ list A ⊢ᶜ⦂ D ! ε}
            → (P' : toCtx 𝕊' ⊢ᶜ⦂ D ! ε)
            → matchL U `nil M₀ `cons N₀ ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
            → Sim es P' (MATCHL {V = U} {M = M₀} {N = N₀})
⟶-≐ˢ-matchL es P' eM with cast-matchL⁻ (sym (toCtx-≐ˢ es)) P' eM
... | U' , M₀' , N₀' , refl , eU , eM₀ , eN₀ =
    _ , _ , es , MATCHL , id-≤≐
  , trans (cong₃ (λ u m n → matchL-reduct (listᵛ u) m n) eU eM₀ eN₀)
      (trans (cong (λ l → matchL-reduct l _ _) (listᵛ-cast (sym (toCtx-≐ˢ es)) U'))
             (cast-matchL-reduct (sym (toCtx-≐ˢ es)) (listᵛ U') M₀' N₀'))

-- sum elimination: likewise, by `injᵛ-cast`.

⟶-≐ˢ-match+ : ∀ {A B D ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
            → {U : toCtx 𝕊 ⊢ᵛ⦂ A |+| B}
            → {M₀ : toCtx 𝕊 ∷ A ⊢ᶜ⦂ D ! ε} → {N₀ : toCtx 𝕊 ∷ B ⊢ᶜ⦂ D ! ε}
            → (P' : toCtx 𝕊' ⊢ᶜ⦂ D ! ε)
            → match+ U `inl M₀ `inr N₀ ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
            → Sim es P' (MATCH+ {V = U} {M = M₀} {N = N₀})
⟶-≐ˢ-match+ es P' eM with cast-match+⁻ (sym (toCtx-≐ˢ es)) P' eM
... | U' , M₀' , N₀' , refl , eU , eM₀ , eN₀ =
    _ , _ , es , MATCH+ , id-≤≐
  , trans (cong₃ (λ u m n → match+-reduct (injᵛ u) m n) eU eM₀ eN₀)
      (trans (cong (λ s → match+-reduct s _ _) (injᵛ-cast (sym (toCtx-≐ˢ es)) U'))
             (cast-match+-reduct (sym (toCtx-≐ˢ es)) (injᵛ U') M₀' N₀'))

⟶-≐ˢ-recL : ∀ {A B ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
          → {U : toCtx 𝕊 ⊢ᵛ⦂ list A} → {M₀ : toCtx 𝕊 ⊢ᶜ⦂ B ! ε}
          → {N₀ : (toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ A ∷ list A) ⟨ ∣ ε ∣ᵉ ⟩ ∷ B ⊢ᶜ⦂ B ! ε}
          → {p : ε ·ₑ ε ≾ₑ ε}
          → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε)
          → recL U M₀ N₀ p ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
          → Sim es P' (RECL {V = U} {M = M₀} {N = N₀} {p = p})
⟶-≐ˢ-recL es {p = p} P' eM with cast-recL⁻ (sym (toCtx-≐ˢ es)) P' eM
... | U' , M₀' , N₀' , refl , eU , eM₀ , eN₀ =
    _ , _ , es , RECL , id-≤≐
  , trans (cong₃ (λ u m n → recL-reduct (listᵛ u) m n p) eU eM₀ eN₀)
      (trans (cong (λ l → recL-reduct l _ _ p) (listᵛ-cast (sym (toCtx-≐ˢ es)) U'))
             (cast-recL-reduct (sym (toCtx-≐ˢ es)) (listᵛ U') M₀' N₀' p))

-- comparison at a scrutinised boolean: the operands correspond on both
-- sides, and so do their data, hence the constants decided to
-- (`cast-decide`).

⟶-≐ˢ-cmp : ∀ {A B ε ⋈} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
         → {U W : toCtx 𝕊 ⊢ᵛ⦂ A} → {et : Et A} → {M N : toCtx 𝕊 ⊢ᶜ⦂ B ! ε}
         → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε)
         → (if cmp ⋈ U W et `then M `else N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
         → Sim es P' (CMP {⋈ = ⋈} {V = U} {W = W} {et = et} {M = M} {N = N})
⟶-≐ˢ-cmp {⋈ = ⋈} es {et = et} P' eM with cast-if⁻ (sym (toCtx-≐ˢ es)) P' eM
... | Vb' , M₀' , N₀' , refl , eVb , eM₀ , eN₀
  with cast-cmp⁻ (sym (toCtx-≐ˢ es)) Vb' eVb
...   | U' , W' , refl , refl , refl =
    _ , _ , es , CMP , id-≤≐
  , trans (cong₃ (λ v m n → if v `then m `else n)
                 (cast-decide (sym (toCtx-≐ˢ es)) ⋈ U' W' et) eM₀ eN₀)
          (sym (cast-if (sym (toCtx-≐ˢ es))))

-- matching: the scrutinee corresponds on both sides, and its two projections
-- commute with the cast (`fstᵛ-cast`/`sndᵛ-cast`).

⟶-≐ˢ-match : ∀ {A B D ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
          → {U : toCtx 𝕊 ⊢ᵛ⦂ A |×| B}
          → {M₀ : toCtx 𝕊 ∷ A ∷ B ⊢ᶜ⦂ D ! ε}
          → (P' : toCtx 𝕊' ⊢ᶜ⦂ D ! ε)
          → (match U `with M₀) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
          → Sim es P' (MATCH {P = U} {M = M₀})
⟶-≐ˢ-match es P' eM with cast-match⁻ (sym (toCtx-≐ˢ es)) P' eM
... | U' , M₀' , refl , eU , eM₀ =
    _ , _ , es , MATCH , id-≤≐
  , subst (λ z → _ ≡ z)
      (cast-match-reduct (sym (toCtx-≐ˢ es)) M₀' (fstᵛ U') (sndᵛ U'))
      (sub-≡ᶜ split-[]
        (trans (cong fstᵛ eU) (fstᵛ-cast (sym (toCtx-≐ˢ es)) U'))
        (sub-≡ᶜ split-[]
          (V-rename-cong wk-ren
            (trans (cong sndᵛ eU) (sndᵛ-cast (sym (toCtx-≐ˢ es)) U')))
          eM₀))

-- sequencing a returned value: the continuation is retyped by a renaming that
-- mentions the context, so `cast-seq-ret` is what moves the cast past it.

⟶-≐ˢ-seq-ret : ∀ {A B ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
            → {V : toCtx 𝕊 ⊢ᵛ⦂ A} → {N : toCtx 𝕊 ⟨ ∣ 𝟏ₑ ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε}
            → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! (𝟏ₑ ·ₑ ε))
            → (return V ⨟ N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
            → Sim es P' (SEQ-RET {V = V} {N = N})
⟶-≐ˢ-seq-ret es P' eM with cast-seq⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M₁' , N' , refl , eM₁ , eN with cast-return⁻ (sym (toCtx-≐ˢ es)) M₁' eM₁
...   | V' , refl , eV =
    _ , _ , es , SEQ-RET , id-≤≐
  , subst (λ z → _ ≡ z) (cast-seq-ret (sym (toCtx-≐ˢ es)) N' V')
      (sub-≡ᶜ split-[] eV (C-rename-cong (cong-∷-ren _) eN))

-- handling a returned value: as `SEQ-RET`, with the handler discarded.

⟶-≐ˢ-handle-ret : ∀ {A B ε} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
               → {V : toCtx 𝕊 ⊢ᵛ⦂ A}
               → {H : (op : Op) → (ε' : E) →
                        toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                          ∷ [ ∣ op-grade op ∣ᵉ ]
                              (⌜ arity op ⌝ᵍ ⇒ B ! ε')
                        ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε')}
               → {N : toCtx 𝕊 ⟨ ∣ 𝟏ₑ ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε}
               → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! (𝟏ₑ ·ₑ ε))
               → (handle return V `with H `in N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
               → Sim es P' (HANDLE-RET {V = V} {H = H} {N = N})
⟶-≐ˢ-handle-ret es P' eM with cast-handle⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M₁' , W' , refl , eM₁ , eW
  with cast-handler⁻ (sym (toCtx-≐ˢ es)) W' eW
...   | H' , N' , refl , eH , eN
  with cast-return⁻ (sym (toCtx-≐ˢ es)) M₁' eM₁
...     | V' , refl , eV =
    _ , _ , es , HANDLE-RET , id-≤≐
  , subst (λ z → _ ≡ z) (cast-seq-ret (sym (toCtx-≐ˢ es)) N' V')
      (sub-≡ᶜ split-[] eV (C-rename-cong (cong-∷-ren _) eN))

-- unboxing: the store is read at the same cell, so the substituted values are
-- related (`unbox-lookup-≐ˢ`).

⟶-≐ˢ-unbox : ∀ {A A₀ D ε ρ ρ'} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
          → {x : [ ρ ] A₀ ∈[ ρ' ] toCtx 𝕊} → {rel : ρ' ≾ᵣ ρ} → {p : A₀ <:ᵛ A}
          → {M₀ : toCtx 𝕊 ∷ A ⊢ᶜ⦂ D ! ε}
          → (P' : toCtx 𝕊' ⊢ᶜ⦂ D ! ε)
          → unbox x rel p M₀ ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
          → Sim es P' (UNBOX {z = x} {rel = rel} {p = p} {M = M₀})
⟶-≐ˢ-unbox {𝕊 = 𝕊} {𝕊' = 𝕊'} es {x = x} {rel = rel} {p = p} P' eM
  with cast-unbox⁻ (sym (toCtx-≐ˢ es)) P' eM
... | _ , x' , rel' , p' , M₀' , refl , hw , eM₀ =
    _ , _ , es , UNBOX , id-≤≐
  , subst (λ z → _ ≡ z)
      (cast-app-reduct (sym (toCtx-≐ˢ es)) M₀'
        (subV (unbox-lookup 𝕊' x' rel') p'))
      (sub-≡ᶜ split-[]
        (trans (cong₂ subV
                 (unbox-lookup-≐ˢ es {x = x} {x' = x'} {rel = rel} {rel' = rel'} hw)
                 (<:ᵛ-irrelevant p p'))
               (sym (cast-subV (sym (toCtx-≐ˢ es)))))
        eM₀)

-- sequencing an operation: the operation floats out, its continuation gaining
-- the sequel. The reduct is retyped in its effect (`ε-subst`) as well.

ε-subst-≡ : ∀ {Γ A ε ε'} → (e : ε ≡ ε') → {M M' : Γ ⊢ᶜ⦂ A ! ε}
          → M ≡ M' → ε-subst e M ≡ ε-subst e M'
ε-subst-≡ refl eM = eM

cast-seq-op : ∀ {Γ Γ' A B ε ε'} {op : Op} → (e : Γ' ≡ Γ)
            → (V' : Γ' ⊢ᵛ⦂ ⌜ param op ⌝ᵍ)
            → (M' : Γ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
                      ⊢ᶜ⦂ A ! ε)
            → (N' : Γ' ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε')
            → ε-≃ (≃ₑ-sym (·ₑ-assoc (op-grade op) ε ε'))
                (perform op (castᵛ e V')
                  ((castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ∣ op-grade op ∣ᵉ ⟩
                                          ∷ ⌜ arity op ⌝ᵍ) e) M')
                    ⨟ C-rename
                        (cong-∷-ren ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ) ∘ʳ ⟨⟩-μ-ren)
                                     ∘ʳ cong-⟨⟩-ren wk-ren))
                        (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A) e)
                               N')))
            ≡ castᶜ e
                (ε-≃ (≃ₑ-sym (·ₑ-assoc (op-grade op) ε ε'))
                  (perform op V'
                    (M' ⨟ C-rename
                            (cong-∷-ren ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ)
                                          ∘ʳ ⟨⟩-μ-ren)
                                         ∘ʳ cong-⟨⟩-ren wk-ren))
                            N')))
cast-seq-op refl V' M' N' = refl

⟶-≐ˢ-seq-op : ∀ {A B ε ε'} {op : Op} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
           → {V : toCtx 𝕊 ⊢ᵛ⦂ ⌜ param op ⌝ᵍ}
           → {M₀ : toCtx 𝕊 ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
                     ⊢ᶜ⦂ A ! ε}
           → {N : toCtx 𝕊 ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'}
           → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! ((op-grade op ·ₑ ε) ·ₑ ε'))
           → (perform op V M₀ ⨟ N) ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
           → Sim es P' (SEQ-OP {V = V} {M = M₀} {N = N})
⟶-≐ˢ-seq-op es P' eM with cast-seq⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M₁' , N' , refl , eM₁ , eN
  with cast-perform⁻ (sym (toCtx-≐ˢ es)) M₁' eM₁
...   | V' , M₀' , refl , eV , eM₀ =
    _ , _ , es , SEQ-OP , id-≤≐
  , subst (λ z → _ ≡ z) (cast-seq-op (sym (toCtx-≐ˢ es)) V' M₀' N')
      (cong (coerce _)
        (cong₂ (perform _) eV (cong₂ _⨟_ eM₀ (C-rename-cong (cong-∷-ren _) eN))))

cast-rename-∷ : ∀ {Γ₁ Γ₂ Γ₁' Γ₂' A C} → (e₁ : Γ₁' ≡ Γ₁) → (e₂ : Γ₂' ≡ Γ₂)
              → (r' : Ren [] Γ₂' Γ₁') → (M' : Γ₁' ∷ A ⊢ᶜ⦂ C)
              → C-rename (cong-∷-ren (castʳ² e₁ e₂ r'))
                  (castᶜ (cong (_∷ A) e₁) M')
              ≡ castᶜ (cong (_∷ A) e₂) (C-rename (cong-∷-ren r') M')
cast-rename-∷ refl refl r' M' = refl

-- The same for a clause: `HANDLE-STEP` retypes it by a renaming under the
-- barrier and the clause's two binders.

cast-rename-cl : ∀ {Γ₁ Γ₂ Γ₁' Γ₂' A A₀ C} → (e₁ : Γ₁' ≡ Γ₁) → (e₂ : Γ₂' ≡ Γ₂)
               → (r' : Ren [] (Γ₂' ⟨ ⊤ᵣ ⟩) (Γ₁' ⟨ ⊤ᵣ ⟩))
               → (M' : Γ₁' ⟨ ⊤ᵣ ⟩ ∷ A ∷ A₀ ⊢ᶜ⦂ C)
               → C-rename (cong-∷-ren (cong-∷-ren
                   (castʳ² (cong (_⟨ ⊤ᵣ ⟩) e₁) (cong (_⟨ ⊤ᵣ ⟩) e₂) r')))
                   (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ⊤ᵣ ⟩ ∷ A ∷ A₀) e₁) M')
               ≡ castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ⊤ᵣ ⟩ ∷ A ∷ A₀) e₂)
                   (C-rename (cong-∷-ren (cong-∷-ren r')) M')
cast-rename-cl refl refl r' M' = refl

-- `HANDLE-OP`'s reduct in one lemma: the cast moves past the box, the lambda,
-- the inner handle, the three renamings and the substitution of the parameter.
-- The fired clause crosses the barrier by a renaming, so nothing is retyped.

cast-handle-op : ∀ {Γ Γ' A B ε ε''} {op : Op} → (e : Γ' ≡ Γ)
               → (V' : Γ' ⊢ᵛ⦂ ⌜ param op ⌝ᵍ)
               → (M' : Γ' ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
                         ⊢ᶜ⦂ A ! ε)
               → (H' : (op' : Op) → (ε' : E) →
                         Γ' ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op' ⌝ᵍ
                           ∷ [ ∣ op-grade op' ∣ᵉ ]
                               (⌜ arity op' ⌝ᵍ ⇒ B ! ε')
                         ⊢ᶜ⦂ B ! (op-grade op' ·ₑ ε'))
               → (N' : Γ' ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε'')
               → box _ (fun
                       (handle (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ∣ op-grade op ∣ᵉ ⟩
                                                      ∷ ⌜ arity op ⌝ᵍ)
                                            e) M')
                       `with (λ op' ε' →
                                C-rename
                                  (cong-∷-ren (cong-∷-ren
                                    (barrier-wk-ren ∣ op-grade op ∣ᵉ
                                                    ⌜ arity op ⌝ᵍ)))
                                  (castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ⊤ᵣ ⟩
                                                         ∷ ⌜ param op' ⌝ᵍ
                                                         ∷ [ ∣ op-grade op' ∣ᵉ ]
                                                             (⌜ arity op' ⌝ᵍ
                                                                ⇒ B ! ε'))
                                               e)
                                         (H' op' ε')))
                       `in (C-rename
                             (  cong-∷-ren ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ)
                             ∘ʳ ⟨⟩-μ-ren)
                             ∘ʳ cong-⟨⟩-ren wk-ren))
                             (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A)
                                          e) N'))))
                      (C-rename (cong-∷-ren (cong-∷-ren barrier-ren))
                        (castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                                               ∷ [ ∣ op-grade op ∣ᵉ ]
                                                   (⌜ arity op ⌝ᵍ
                                                      ⇒ B ! (ε ·ₑ ε'')))
                                     e)
                               (H' op (ε ·ₑ ε'')))
                       [ castᵛ e V' ]₁)
               ≡ castᶜ e
                   (box _ (fun
                          (handle M'
                          `with (λ op' ε' →
                                   C-rename
                                     (cong-∷-ren (cong-∷-ren
                                       (barrier-wk-ren ∣ op-grade op ∣ᵉ
                                                       ⌜ arity op ⌝ᵍ)))
                                     (H' op' ε'))
                          `in (C-rename
                                (  cong-∷-ren ((⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ)
                                ∘ʳ ⟨⟩-μ-ren)
                                ∘ʳ cong-⟨⟩-ren wk-ren))
                                N')))
                         (C-rename (cong-∷-ren (cong-∷-ren barrier-ren))
                                   (H' op (ε ·ₑ ε''))
                          [ V' ]₁))
cast-handle-op refl V' M' H' N' = refl

-- `HANDLE-OP` fires a clause: the state is unchanged, and every piece of the
-- reduct is a congruence for `_≡_`.

⟶-≐ˢ-handle-op : ∀ {A B ε ε''} {op : Op} {𝕊 𝕊' : State []} → (es : 𝕊 ≐ˢ 𝕊')
              → {V : toCtx 𝕊 ⊢ᵛ⦂ ⌜ param op ⌝ᵍ}
              → {M₀ : toCtx 𝕊 ⟨ ∣ op-grade op ∣ᵉ ⟩
                        ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ A ! ε}
              → {H : (op' : Op) → (ε' : E) →
                       toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op' ⌝ᵍ
                         ∷ [ ∣ op-grade op' ∣ᵉ ]
                             (⌜ arity op' ⌝ᵍ ⇒ B ! ε')
                       ⊢ᶜ⦂ B ! (op-grade op' ·ₑ ε')}
              → {N : toCtx 𝕊 ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε''}
              → (P' : toCtx 𝕊' ⊢ᶜ⦂ B ! ((op-grade op ·ₑ ε) ·ₑ ε''))
              → (handle perform op V M₀ `with H `in N)
                  ≡ castᶜ (sym (toCtx-≐ˢ es)) P'
              → Sim es P' (HANDLE-OP {V = V} {M = M₀} {H = H} {N = N})

⟶-≐ˢ-handle-op {A = A} {B = B} {ε = ε} {ε'' = ε''} {op = op} {𝕊 = 𝕊} {𝕊' = 𝕊'}
              es P' eM
  with cast-handle⁻ (sym (toCtx-≐ˢ es)) P' eM
... | M₁' , W' , refl , eM₁ , eW
  with cast-handler⁻ (sym (toCtx-≐ˢ es)) W' eW
...   | H' , N' , refl , eH , eN
  with cast-perform⁻ (sym (toCtx-≐ˢ es)) M₁' eM₁
...     | V' , M₀' , refl , eV , eM₀ =
    _ , _ , es , HANDLE-OP , id-≤≐
  , subst (λ z → _ ≡ z)
      (cast-handle-op (sym (toCtx-≐ˢ es)) V' M₀' H' N')
      (cong₂ (box _)
        (cong fun
          (cong₂ handle_`with_ eM₀
            (handler-≡
              (C-rename-cong (cong-∷-ren _) eN)
              (λ op' ε' →
                 C-rename-cong (cong-∷-ren (cong-∷-ren
                                 (barrier-wk-ren ∣ op-grade op ∣ᵉ
                                                 ⌜ arity op ⌝ᵍ)))
                               (eH op' ε')))))
        (sub-≡ᶜ (split-∷ split-[]) eV
          (C-rename-cong (cong-∷-ren (cong-∷-ren barrier-ren))
                         (eH op (ε ·ₑ ε'')))))

-- `HANDLE-STEP`: as `SEQ-STEP`, plus the clause retyping. The scrutinee's
-- simulation is passed in, as the recursion supplies it.

⟶-≐ˢ-handle-step : ∀ {A A₁ B ε₁ ε₂ ε₁'} {𝕊 𝕊' 𝕊₁ : State []} → (es : 𝕊 ≐ˢ 𝕊')
                → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε₁}
                → {H : (op : Op) → (ε₃ : E) →
                         toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                           ∷ [ ∣ op-grade op ∣ᵉ ]
                               (⌜ arity op ⌝ᵍ ⇒ B ! ε₃)
                         ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε₃)}
                → {N : toCtx 𝕊 ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε₂}
                → {M₁ : toCtx 𝕊₁ ⊢ᶜ⦂ A₁ ! ε₁'}
                → (M' : toCtx 𝕊' ⊢ᶜ⦂ A ! ε₁)
                → (H' : (op : Op) → (ε₃ : E) →
                          toCtx 𝕊' ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                            ∷ [ ∣ op-grade op ∣ᵉ ]
                                (⌜ arity op ⌝ᵍ ⇒ B ! ε₃)
                          ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε₃))
                → (N' : toCtx 𝕊' ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε₂)
                → (∀ op ε₃ → H op ε₃
                     ≡ castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                                              ∷ [ ∣ op-grade op ∣ᵉ ]
                                                  (⌜ arity op ⌝ᵍ ⇒ B ! ε₃))
                               (sym (toCtx-≐ˢ es)))
                              (H' op ε₃))
                → N ≡ castᶜ (cong (λ Γ₁ → Γ₁ ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A) (sym (toCtx-≐ˢ es))) N'
                → (r : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊₁ ∣ M₁ ⟩)
                → (c : κₛ (step-extends-state r) ·ᵣ ∣ ε₁' ∣ᵉ ≾ᵣ ∣ ε₁ ∣ᵉ)
                → Sim es M' r
                ----------------------------------------------------------------
                → Sim es (handle M' `with H' `in N')
                         (HANDLE-STEP {H = H} {N = N} r c)

⟶-≐ˢ-handle-step {A = A} {ε₁ = ε₁} {ε₁' = ε₁'} {𝕊 = 𝕊} {𝕊' = 𝕊'}
                {𝕊₁ = 𝕊₁} es M' H' N' eH eN r c
                (𝕊₂' , M₂' , es₂ , r' , h , eM₂) =
    𝕊₂' , _ , es₂ , HANDLE-STEP r' (step-grade-≾ r') , h
  , subst (λ z → _ ≡ z)
      (sym (trans (cast-handle (sym (toCtx-≐ˢ es₂)) {M = M₂'})
                  (cong (handle castᶜ (sym (toCtx-≐ˢ es₂)) M₂' `with_)
                        (cast-handler (sym (toCtx-≐ˢ es₂))))))
      (cong₂ handle_`with_ eM₂ (handler-≡
        (trans
          (cong₂ subCtx
            (<:ᵛ-irrelevant (step-refines-type r) (step-refines-type r'))
            (trans
              (C-rename-≡
                (cong-∷-ren-≐ʳ (suc-comp-ren-≐ʳ h es es₂ c (step-grade-≾ r'))) _)
              (subst (λ z → _ ≡ z)
                (trans (cast-rename-∷ (cong (_⟨ ∣ ε₁ ∣ᵉ ⟩) (sym (toCtx-≐ˢ es)))
                                      (cong (_⟨ ∣ ε₁' ∣ᵉ ⟩) (sym (toCtx-≐ˢ es₂)))
                                      (suc-comp-ren (step-extends-state r')
                                                    (step-grade-≾ r'))
                                      N')
                       (castᶜ-irr
                         (cong (_∷ A) (cong (_⟨ ∣ ε₁' ∣ᵉ ⟩) (sym (toCtx-≐ˢ es₂))))
                         (cong (λ Γ₀ → Γ₀ ⟨ ∣ ε₁' ∣ᵉ ⟩ ∷ A) (sym (toCtx-≐ˢ es₂)))
                         (C-rename (cong-∷-ren (suc-comp-ren
                                     (step-extends-state r')
                                     (step-grade-≾ r'))) N')))
                (C-rename-cong (cong-∷-ren _)
                  (subst (λ z → _ ≡ z) (castᶜ-irr _ _ N') eN)))))
          (subCtx-cast (λ Γ₀ → Γ₀ ⟨ ∣ ε₁' ∣ᵉ ⟩) (sym (toCtx-≐ˢ es₂))
            (step-refines-type r')
            (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r')
                                                (step-grade-≾ r'))) N')))
        (λ op ε₃ →
           trans
             (C-rename-≡
               (cong-∷-ren-≐ʳ (cong-∷-ren-≐ʳ
                 (suc-comp-ren-≐ʳ h es es₂ (≾-⊤ᵣ _) (≾-⊤ᵣ _)))) _)
             (trans
               (C-rename-cong
                 (cong-∷-ren (cong-∷-ren
                   (castʳ² (cong (_⟨ ⊤ᵣ ⟩) (sym (toCtx-≐ˢ es)))
                           (cong (_⟨ ⊤ᵣ ⟩) (sym (toCtx-≐ˢ es₂)))
                           (suc-comp-ren (step-extends-state r') (≾-⊤ᵣ _)))))
                 (eH op ε₃))
               (cast-rename-cl (sym (toCtx-≐ˢ es)) (sym (toCtx-≐ˢ es₂))
                               (suc-comp-ren (step-extends-state r')
                                             (≾-⊤ᵣ _))
                               (H' op ε₃))))))

-- One clause per rule. The two congruences recurse, and hand the
-- recursion's `_≤≐_` witness on.

⟶-≐ˢ : ∀ {A A₁ ε ε₁} {𝕊 𝕊' 𝕊₁ : State []}
    → (es : 𝕊 ≐ˢ 𝕊')
    → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → {M' : toCtx 𝕊' ⊢ᶜ⦂ A ! ε}
    → M ≡ castᶜ (sym (toCtx-≐ˢ es)) M'
    → {N : toCtx 𝕊₁ ⊢ᶜ⦂ A₁ ! ε₁}
    → (r : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊₁ ∣ N ⟩)
    -------------------------------
    → Sim es M' r

⟶-≐ˢ es eM APP         = ⟶-≐ˢ-app es _ eM
⟶-≐ˢ es eM MATCH       = ⟶-≐ˢ-match es _ eM
⟶-≐ˢ es eM CMP         = ⟶-≐ˢ-cmp es _ eM
⟶-≐ˢ es eM MATCHL      = ⟶-≐ˢ-matchL es _ eM
⟶-≐ˢ es eM RECL        = ⟶-≐ˢ-recL es _ eM
⟶-≐ˢ es eM IF-TRUE     = ⟶-≐ˢ-if-true es _ eM
⟶-≐ˢ es eM IF-FALSE    = ⟶-≐ˢ-if-false es _ eM
⟶-≐ˢ es eM MATCHℕ-ZERO = ⟶-≐ˢ-matchℕ-zero es _ eM
⟶-≐ˢ es eM MATCHℕ-SUCC = ⟶-≐ˢ-matchℕ-succ es _ eM
⟶-≐ˢ es eM RECℕ-ZERO   = ⟶-≐ˢ-recℕ-zero es _ eM
⟶-≐ˢ es eM RECℕ-SUCC   = ⟶-≐ˢ-recℕ-succ es _ eM
⟶-≐ˢ es eM MATCH+      = ⟶-≐ˢ-match+ es _ eM
⟶-≐ˢ es eM SEQ-RET     = ⟶-≐ˢ-seq-ret es _ eM
⟶-≐ˢ es eM SEQ-OP      = ⟶-≐ˢ-seq-op es _ eM
⟶-≐ˢ es eM DELAY       = ⟶-≐ˢ-delay es _ eM
⟶-≐ˢ es eM HANDLE-RET  = ⟶-≐ˢ-handle-ret es _ eM
⟶-≐ˢ es eM HANDLE-OP   = ⟶-≐ˢ-handle-op es _ eM
⟶-≐ˢ es eM BOX         = ⟶-≐ˢ-box es _ eM
⟶-≐ˢ es eM UNBOX       = ⟶-≐ˢ-unbox es _ eM
⟶-≐ˢ es eM SUB-APP     = ⟶-≐ˢ-sub-app es _ eM
⟶-≐ˢ es eM SUB-HANDLE  = ⟶-≐ˢ-sub-handle es _ eM
⟶-≐ˢ es eM SUB-HANDLE-TRANS = ⟶-≐ˢ-sub-handle-trans es _ eM
⟶-≐ˢ es eM SUB-IF      = ⟶-≐ˢ-sub-if es _ eM
⟶-≐ˢ es eM SUB-MATCHℕ  = ⟶-≐ˢ-sub-matchℕ es _ eM
⟶-≐ˢ es eM SUB-RECℕ    = ⟶-≐ˢ-sub-recℕ es _ eM
⟶-≐ˢ es eM SUB         = ⟶-≐ˢ-sub es _ eM

-- sequencing: simulate the head, then rebuild
⟶-≐ˢ es eM (SEQ-STEP {ε₁ = ε₁} {ε₃ = ε₃} {A = A} r c)
  with cast-seq⁻ (sym (toCtx-≐ˢ es)) _ eM
... | M₁' , N' , refl , eM₁ , eN with ⟶-≐ˢ es eM₁ r
...   | 𝕊₂' , M₂' , es₂ , r' , h , eM₂ =
    𝕊₂' , _ , es₂ , SEQ-STEP r' (step-grade-≾ r') , h
  , subst (λ z → _ ≡ z)
      (sym (cast-seq (sym (toCtx-≐ˢ es₂)) {M = M₂'}
             {N = subCtx (step-refines-type r')
                    (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r')
                                                        (step-grade-≾ r'))) N')}))
    (cong₂ _⨟_ eM₂
      (trans
        (cong₂ subCtx
          (<:ᵛ-irrelevant (step-refines-type r) (step-refines-type r'))
          (trans
            (C-rename-≡
              (cong-∷-ren-≐ʳ (suc-comp-ren-≐ʳ h es es₂ c (step-grade-≾ r'))) _)
            (subst (λ z → _ ≡ z)
              (trans (cast-rename-∷ (cong (_⟨ ∣ ε₁ ∣ᵉ ⟩) (sym (toCtx-≐ˢ es)))
                                    (cong (_⟨ ∣ ε₃ ∣ᵉ ⟩) (sym (toCtx-≐ˢ es₂)))
                                    (suc-comp-ren (step-extends-state r')
                                                  (step-grade-≾ r'))
                                    N')
                     (castᶜ-irr
                       (cong (_∷ A) (cong (_⟨ ∣ ε₃ ∣ᵉ ⟩) (sym (toCtx-≐ˢ es₂))))
                       (cong (λ Γ₀ → Γ₀ ⟨ ∣ ε₃ ∣ᵉ ⟩ ∷ A) (sym (toCtx-≐ˢ es₂)))
                       (C-rename (cong-∷-ren (suc-comp-ren
                                   (step-extends-state r')
                                   (step-grade-≾ r'))) N')))
              (C-rename-cong (cong-∷-ren _)
                (subst (λ z → _ ≡ z) (castᶜ-irr _ _ N') eN)))))
        (subCtx-cast (λ Γ₀ → Γ₀ ⟨ ∣ ε₃ ∣ᵉ ⟩) (sym (toCtx-≐ˢ es₂))
          (step-refines-type r')
          (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r')
                                              (step-grade-≾ r'))) N'))))

⟶-≐ˢ es eM (HANDLE-STEP r c) with cast-handle⁻ (sym (toCtx-≐ˢ es)) _ eM
... | M₁' , W' , refl , eM₁ , eW with cast-handler⁻ (sym (toCtx-≐ˢ es)) W' eW
...   | H' , N' , refl , eH , eN =
  ⟶-≐ˢ-handle-step es M₁' H' N' eH eN r c (⟶-≐ˢ es eM₁ r)

-- The bisimulation extends to runs, step by step.

⟶*-≐ˢ : ∀ {A A₁ ε ε₁} {𝕊 𝕊' 𝕊₁ : State []}
     → (es : 𝕊 ≐ˢ 𝕊')
     → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → {M' : toCtx 𝕊' ⊢ᶜ⦂ A ! ε}
     → M ≡ castᶜ (sym (toCtx-≐ˢ es)) M'
     → {N : toCtx 𝕊₁ ⊢ᶜ⦂ A₁ ! ε₁}
     → ⟨ 𝕊 ∣ M ⟩ ⟶* ⟨ 𝕊₁ ∣ N ⟩
     -------------------------------------------------------------------
     → Σ[ 𝕊₁' ∈ State [] ] Σ[ N' ∈ (toCtx 𝕊₁' ⊢ᶜ⦂ A₁ ! ε₁) ]
       Σ[ es₁ ∈ 𝕊₁ ≐ˢ 𝕊₁' ]
         (⟨ 𝕊' ∣ M' ⟩ ⟶* ⟨ 𝕊₁' ∣ N' ⟩)
       × (N ≡ castᶜ (sym (toCtx-≐ˢ es₁)) N')

⟶*-≐ˢ {𝕊' = 𝕊'} es {M' = M'} eM done = 𝕊' , M' , es , done , eM
⟶*-≐ˢ es eM (r ▸ rs) with ⟶-≐ˢ es eM r
... | 𝕊₂' , N₂' , es₂ , r' , _ , eN₂ with ⟶*-≐ˢ es₂ eN₂ rs
...   | 𝕊₁' , N' , es₁ , rs' , eN = 𝕊₁' , N' , es₁ , r' ▸ rs' , eN

