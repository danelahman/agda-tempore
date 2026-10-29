------------------------------------------------------------------
-- Type safety of the reduction                                 --
--                                                              --
-- A configuration whose state a state typing `Σ` types, and    --
-- whose term is typed in the context of the state at `X ‼ ε`,  --
-- has finished, returning a value or calling an operation, or  --
-- steps (`progress`). A step extends the state by passages of  --
-- grade `δₛ e`, and an extension `Σ'` of `Σ` types the new     --
-- state, the new term being typed at `X' ‼ ε'` with `X' <: X`  --
-- and `δₛ e · ∣ ε' ∣ ≾ ∣ ε ∣` (`preservation`). A handled       --
-- operation call runs its clause at the grade `ε_M · ε'` of    --
-- the rest of the handled computation followed by the return   --
-- clause.                                                      --
------------------------------------------------------------------

open import Data.Bool.Base using () renaming (true to tt𝔹; false to ff𝔹)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Grades.Base
open import Language.Spec
open import Language.Operations
open import Language.Comparisons using (Cmp; holds)

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Semantics.TypeSafety (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OpenCalculus.Syntax.Grades            S
open import OpenCalculus.Syntax.Types             S
open import OpenCalculus.Syntax.Contexts          S
open import OpenCalculus.Hypotheses               S
open import OpenCalculus.Typing                   S
open import OpenCalculus.Typing.Erasure           S
open import OpenCalculus.Typing.GradeSubstitution S
open import OpenCalculus.Typing.Renaming          S
open import OpenCalculus.Typing.Substitution      S
open import OpenCalculus.Typing.Inversion         S
open import OpenCalculus.Typing.ScopeClosed       S
open import OpenCalculus.Syntax.Run               S
open import OpenCalculus.Semantics.States         S
open import OpenCalculus.Semantics.Reduction      S

------------------------------------------------------------------------
-- Grades

private

  module _ {Θ : Scope} {Q : Hyps Θ} where

    û≾∣∣ : ∀ {ε} → Q ⊩ ûₑ ≾̂ₑ ε → Q ⊩ ûᵣ ≾̂ᵣ ∣ ε ∣̂ᵉ
    û≾∣∣ p = transᵣ (eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-const (≃ᵣ-sym map-uᵉ)) (≡̂ᵣ-sym ≡̂ᵣ-map-const)))
                    (map-mono p)

    ∣·∣ : ∀ {ε ε'} → Q ⊩ ∣ ε ∣̂ᵉ ·̂ᵣ ∣ ε' ∣̂ᵉ ≾̂ᵣ ∣ ε ·̂ₑ ε' ∣̂ᵉ
    ∣·∣ = eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-map-·)

    ·∣∣ : ∀ {ε ε'} → Q ⊩ ∣ ε ·̂ₑ ε' ∣̂ᵉ ≾̂ᵣ ∣ ε ∣̂ᵉ ·̂ᵣ ∣ ε' ∣̂ᵉ
    ·∣∣ = eqᵣ ≡̂ᵣ-map-·

    ∣const∣ : ∀ {g} → Q ⊩ rconst (mapᵉ g) ≾̂ᵣ ∣ econst g ∣̂ᵉ
    ∣const∣ = eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-map-const)

    -- an effect above the unit followed by another is above the other

    ≾-·ˡ : ∀ {ε₁ ε₂} → Q ⊩ ûₑ ≾̂ₑ ε₁ → Q ⊩ ε₂ ≾̂ₑ ε₁ ·̂ₑ ε₂
    ≾-·ˡ p = transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-identityˡ)) (monoₑ p ⊩≾̂ₑ-refl)

    -- the grade of a lock and of the time it adds, regrouped

    regroup : ∀ {ρ ε₁ ε₂ ε}
            → Q ⊩ ρ ·̂ᵣ ∣ ε₁ ∣̂ᵉ ≾̂ᵣ ∣ ε ∣̂ᵉ
            → Q ⊩ ρ ·̂ᵣ ∣ ε₁ ·̂ₑ ε₂ ∣̂ᵉ ≾̂ᵣ ∣ ε ·̂ₑ ε₂ ∣̂ᵉ
    regroup p =
      transᵣ (monoᵣ ⊩≾̂ᵣ-refl ·∣∣)
        (transᵣ (eqᵣ (≡̂ᵣ-sym ≡̂ᵣ-assoc)) (transᵣ (monoᵣ p ⊩≾̂ᵣ-refl) ∣·∣))

------------------------------------------------------------------------
-- The statements

-- A step from a configuration

Steps : ∀ {n} → State n → RunC n → Set
Steps S M = Σ[ m ∈ ℕ ] Σ[ S' ∈ State m ] Σ[ M' ∈ RunC m ] ⟨ S ∣ M ⟩↝⟨ S' ∣ M' ⟩

-- What a step preserves

record Preserved {n m} {S : State n} {S' : State m} (e : S ≤ₛ S') (Σ : StateTyping S)
                 (M' : RunC m) (X : OVType ∅ˢ) (ε : EExp ∅ˢ) : Set where
  field
    Σ'      : StateTyping S'
    extends : Σ ⊆[ e ] Σ'
    types   : Types Σ'
    X'      : OVType ∅ˢ
    ε'      : EExp ∅ˢ
    typed   : ctx Σ' ⊢ᶜ M' ⦂ X' ‼ ε'
    subtype : ⊤ᴴ ∣ X' <:̂ᵛ X
    grade   : ⊤ᴴ ⊩ δₛ e ·̂ᵣ ∣ ε' ∣̂ᵉ ≾̂ᵣ ∣ ε ∣̂ᵉ

open Preserved

------------------------------------------------------------------------
-- Auxiliary typings

private

  -- the state unchanged

  stay : ∀ {n} {S : State n} {Σ : StateTyping S} {M' C₁ X ε}
       → Types Σ → (D : ⊤ᴴ ∣ ctx Σ ⊢C⦂ C₁) → ∥ D ∥ᶜ ≡ M' → ⊤ᴴ ∣ C₁ <:̂ᶜ X ‼ ε
       → Preserved ≤ₛ-refl Σ M' X ε
  stay {Σ = Σ} T D eq (p ‼ₛ q) = record
    { Σ' = Σ ; extends = ⊆-refl ; types = T ; typed = D , eq ; subtype = p
    ; grade = transᵣ (eqᵣ ≡̂ᵣ-identityˡ) (map-mono q) }

  -- a handler, in an extended context, at an input grade whose image
  -- the extension's grade does not push above the original's

  retype : ∀ {n m} {Γ : OCtx ∅ˢ n} {Γ' : OCtx ∅ˢ m} {δ A B ε ε₁ ε'}
         → (e : Ext ⊤ᴴ Γ Γ' δ) → ⊤ᴴ ⊩ δ ·̂ᵣ ∣ ε₁ ∣̂ᵉ ≾̂ᵣ ∣ ε ∣̂ᵉ
         → (N : ⊤ᴴ ∣ Γ ⟨ ∣ ε ∣̂ᵉ ⟩ ∷ A ⊢C⦂ B ‼ ε')
         → (H : (op : Op) → wkᵉ-H ⊤ᴴ ∣ clause-ctx Γ B op ⊢C⦂ clause-ty B op)
         → Σ[ D ∈ ⊤ᴴ ∣ Γ' ⊢V⦂ (A ‼ ε₁) ⇛ (B ‼ ε') ]
             ∥ D ∥ᵛ ≡ renᵛ (epos e) (handler ∥ N ∥ᶜ (λ op → ∥ H op ∥ᶜ))
  retype e le N H =
    handler (rename-c (ext-lock e le ⇑ʳ) N) (λ op → rename-c (ext-clause e) (H op)) ,
    cong₂ handler (∥rename-c∥ (ext-lock e le ⇑ʳ) N)
                  (fun-ext (λ op → ∥rename-c∥ (ext-clause e) (H op)))

  -- a decided comparison is a boolean

  decide-typed : ∀ {n} {Γ : OCtx ∅ˢ n} → (⋈ : Cmp) → (V W : RunV n)
               → Γ ⊢ᵛ decide ⋈ V W ⦂ Bool
  decide-typed ⋈ V W with holds ⋈ (compareᴰ (datum V) (datum W))
  ... | tt𝔹 = true , refl
  ... | ff𝔹 = false , refl

------------------------------------------------------------------------
-- Preservation

preservation : ∀ {n m} {S : State n} {S' : State m} {e : S ≤ₛ S'} {Σ : StateTyping S}
                 {M M' X ε}
             → Types Σ → ctx Σ ⊢ᶜ M ⦂ X ‼ ε → ⟨ S ∣ M ⟩↝[ e ]⟨ S' ∣ M' ⟩
             → Preserved e Σ M' X ε

-- functions, data and recursion

preservation T (D , eD) APP with invC≡ D eD
... | _ , (A , (DV , eV) , (DW , eW)) , q₀ with invV≡ DV eV
... | _ , (_ , _ , refl , (DM , eM)) , (p₁ ⇒ₛ q₁) =
  stay T (sub-c here (subV DW p₁) DM)
       (trans (∥sub-c∥ here (subV DW p₁) DM) (cong₂ (subᶜ 0) eW eM))
       (<:̂ᶜ-trans q₁ q₀)

preservation T (D , eD) MATCH with invC≡ D eD
... | _ , (A , B , (DV , eV) , (DM , eM)) , q₀ with invV≡ DV eV
... | _ , (_ , _ , refl , (D₁ , e₁) , (D₂ , e₂)) , (p₁ |×|ₛ p₂) =
  stay T (sub-c here (subV D₂ p₂) M₁)
       (trans (∥sub-c∥ here (subV D₂ p₂) M₁)
              (cong₂ (subᶜ 0) e₂ (trans (∥sub-c∥ (there∷ here) (subV D₁ p₁) DM)
                                        (cong₂ (subᶜ 1) e₁ eM))))
       q₀
  where M₁ = sub-c (there∷ here) (subV D₁ p₁) DM

preservation T (D , eD) (CMP {⋈} {V} {W}) with invC≡ D eD
... | _ , ((DV , eV) , (DM , eM) , (DN , eN)) , q₀ =
  stay T (if proj₁ (decide-typed ⋈ V W) `then DM `else DN)
       (cong₃ if_`then_`else_ (proj₂ (decide-typed ⋈ V W)) eM eN) q₀

preservation T (D , eD) IF-TRUE with invC≡ D eD
... | _ , ((DV , eV) , (DM , eM) , (DN , eN)) , q₀ = stay T DM eM q₀

preservation T (D , eD) IF-FALSE with invC≡ D eD
... | _ , ((DV , eV) , (DM , eM) , (DN , eN)) , q₀ = stay T DN eN q₀

preservation T (D , eD) CASEℕ-ZERO with invC≡ D eD
... | _ , ((DV , eV) , (DM , eM) , (DN , eN)) , q₀ = stay T DM eM q₀

preservation T (D , eD) CASEℕ-SUCC with invC≡ D eD
... | _ , ((DV , eV) , (DM , eM) , (DN , eN)) , q₀ with invV≡ DV eV
... | _ , (refl , (D₁ , e₁)) , _ =
  stay T (sub-c here D₁ DN) (trans (∥sub-c∥ here D₁ DN) (cong₂ (subᶜ 0) e₁ eN)) q₀

preservation T (D , eD) RECℕ-ZERO with invC≡ D eD
... | _ , (B , ε₀ , refl , (DV , eV) , (DM , eM) , (DN , eN) , pε) , q₀ = stay T DM eM q₀

preservation {Σ = Σ} T (D , eD) RECℕ-SUCC with invC≡ D eD
... | _ , (B , ε₀ , refl , (DV , eV) , (DM , eM) , (DN , eN) , pε) , q₀ with invV≡ DV eV
... | _ , (refl , (D₁ , e₁)) , _ =
  stay T (subC (recℕ D₁ DM DN pε ⨟ N₁) (<:̂ᵛ-refl B ‼ₛ pε))
       (cong₂ _⨟_ (cong₃ recℕ e₁ eM eN)
              (trans (∥sub-c∥ (there∷ (there⟨⟩ here)) D₁ (rename-c r DN))
                     (cong₂ (subᶜ 1) e₁
                            (trans (∥rename-c∥ r DN)
                                   (trans (ren-idᶜ (ext-id (ext-id (λ i → refl))) ∥ DN ∥ᶜ) eN)))))
       q₀
  where
    r : Ren ⊤ᴴ ((ctx Σ ⟨ rconst ⊤ᵣ ⟩ ∷ Nat) ⟨ ∣ ε₀ ∣̂ᵉ ⟩ ∷ B) ((ctx Σ ∷ Nat) ⟨ ∣ ε₀ ∣̂ᵉ ⟩ ∷ B)
    r = lockʳ ∣ ε₀ ∣̂ᵉ (lock-remove topᵣ ⇑ʳ) ⇑ʳ
    N₁ = sub-c (there∷ (there⟨⟩ here)) D₁ (rename-c r DN)

preservation T (D , eD) CASE-INL with invC≡ D eD
... | _ , (A , B , (DV , eV) , (DM , eM) , (DN , eN)) , q₀ with invV≡ DV eV
... | _ , (_ , _ , refl , (D₁ , e₁)) , (p₁ |+|ₛ p₂) =
  stay T (sub-c here (subV D₁ p₁) DM)
       (trans (∥sub-c∥ here (subV D₁ p₁) DM) (cong₂ (subᶜ 0) e₁ eM)) q₀

preservation T (D , eD) CASE-INR with invC≡ D eD
... | _ , (A , B , (DV , eV) , (DM , eM) , (DN , eN)) , q₀ with invV≡ DV eV
... | _ , (_ , _ , refl , (D₁ , e₁)) , (p₁ |+|ₛ p₂) =
  stay T (sub-c here (subV D₁ p₂) DN)
       (trans (∥sub-c∥ here (subV D₁ p₂) DN) (cong₂ (subᶜ 0) e₁ eN)) q₀

preservation T (D , eD) CASEL-NIL with invC≡ D eD
... | _ , (A , (DV , eV) , (DM , eM) , (DN , eN)) , q₀ = stay T DM eM q₀

preservation T (D , eD) CASEL-CONS with invC≡ D eD
... | _ , (A , (DV , eV) , (DM , eM) , (DN , eN)) , q₀ with invV≡ DV eV
... | _ , (_ , refl , (D₁ , e₁) , (D₂ , e₂)) , (|List|ₛ p₁) =
  stay T (sub-c here (subV D₂ (|List|ₛ p₁)) N₁)
       (trans (∥sub-c∥ here (subV D₂ (|List|ₛ p₁)) N₁)
              (cong₂ (subᶜ 0) e₂ (trans (∥sub-c∥ (there∷ here) (subV D₁ p₁) DN)
                                        (cong₂ (subᶜ 1) e₁ eN))))
       q₀
  where N₁ = sub-c (there∷ here) (subV D₁ p₁) DN

preservation T (D , eD) RECL-NIL with invC≡ D eD
... | _ , (A , B , ε₀ , refl , (DV , eV) , (DM , eM) , (DN , eN) , pε) , q₀ = stay T DM eM q₀

preservation {Σ = Σ} T (D , eD) RECL-CONS with invC≡ D eD
... | _ , (A , B , ε₀ , refl , (DV , eV) , (DM , eM) , (DN , eN) , pε) , q₀ with invV≡ DV eV
... | _ , (_ , refl , (D₁ , e₁) , (D₂ , e₂)) , (|List|ₛ p₁) =
  stay T (subC (recL (subV D₂ (|List|ₛ p₁)) DM DN pε ⨟ N₂) (<:̂ᵛ-refl B ‼ₛ pε))
       (cong₂ _⨟_ (cong₃ recL e₂ eM eN)
              (trans (∥sub-c∥ (there∷ (there⟨⟩ here)) (subV D₂ (|List|ₛ p₁)) N₁)
                     (cong₂ (subᶜ 1) e₂
                            (trans (∥sub-c∥ (there∷ (there⟨⟩ (there∷ here))) (subV D₁ p₁) N₀)
                                   (cong₂ (subᶜ 2) e₁
                                          (trans (∥rename-c∥ r DN)
                                                 (trans (ren-idᶜ (ext-id (ext-id (ext-id
                                                                   (λ i → refl)))) ∥ DN ∥ᶜ)
                                                        eN)))))))
       q₀
  where
    r : Ren ⊤ᴴ ((ctx Σ ⟨ rconst ⊤ᵣ ⟩ ∷ A ∷ |List| A) ⟨ ∣ ε₀ ∣̂ᵉ ⟩ ∷ B)
               ((ctx Σ ∷ A ∷ |List| A) ⟨ ∣ ε₀ ∣̂ᵉ ⟩ ∷ B)
    r = lockʳ ∣ ε₀ ∣̂ᵉ ((lock-remove topᵣ ⇑ʳ) ⇑ʳ) ⇑ʳ
    N₀ = rename-c r DN
    N₁ = sub-c (there∷ (there⟨⟩ (there∷ here))) (subV D₁ p₁) N₀
    N₂ = sub-c (there∷ (there⟨⟩ here)) (subV D₂ (|List|ₛ p₁)) N₁

-- sequencing

preservation T (D , eD) SEQ-RET with invC≡ D eD
... | _ , (A , B , ε₁ , ε₂ , refl , (DR , eR) , (DN , eN)) , q₀ with invC≡ DR eR
... | _ , (A₃ , refl , (DV , eV)) , (p₃ ‼ₛ q₃) =
  stay T (sub-c here (subV DV p₃) (rename-c r DN))
       (trans (∥sub-c∥ here (subV DV p₃) (rename-c r DN))
              (cong₂ (subᶜ 0) eV (trans (∥rename-c∥ r DN)
                                        (trans (ren-idᶜ (ext-id (λ i → refl)) ∥ DN ∥ᶜ) eN))))
       (<:̂ᶜ-trans (<:̂ᵛ-refl B ‼ₛ ≾-·ˡ q₃) q₀)
  where r = lock-remove (û≾∣∣ q₃) ⇑ʳ

preservation {Σ = Σ} T (D , eD) (SEQ-OP {op}) with invC≡ D eD
... | _ , (A , B , ε₁ , ε₂ , refl , (DP , eP) , (DN , eN)) , q₀ with invC≡ DP eP
... | _ , (A₃ , ε₃ , refl , (DV , eV) , (DM , eM)) , (p₃ ‼ₛ q₃) =
  stay T (perform op DV (subC DM (p₃ ‼ₛ ⊩≾̂ₑ-refl) ⨟ rename-c r DN))
       (cong₂ (perform op) eV (cong₂ _⨟_ eM (trans (∥rename-c∥ r DN) (cong (renᶜ (ext suc)) eN))))
       (<:̂ᶜ-trans (<:̂ᵛ-refl B ‼ₛ transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-assoc)) (monoₑ q₃ ⊩≾̂ₑ-refl)) q₀)
  where
    le : ⊤ᴴ ⊩ rconst (mapᵉ (op-grade op)) ·̂ᵣ ∣ ε₃ ∣̂ᵉ ≾̂ᵣ ∣ ε₁ ∣̂ᵉ
    le = transᵣ (monoᵣ ∣const∣ ⊩≾̂ᵣ-refl) (transᵣ ∣·∣ (map-mono q₃))
    r : Ren ⊤ᴴ (ctx Σ ⟨ ∣ ε₁ ∣̂ᵉ ⟩ ∷ A)
               ((ctx Σ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ) ⟨ ∣ ε₃ ∣̂ᵉ ⟩ ∷ A)
    r = ext-lock (wk-ext lock-ext) le ⇑ʳ

preservation T (D , eD) (SEQ-STEP {e = e} s) with invC≡ D eD
... | _ , (A , B , ε₁ , ε₂ , refl , (DM , eM) , (DN , eN)) , (p₀ ‼ₛ q₀)
    with preservation T (DM , eM) s
... | P = record
  { Σ'      = Σ' P
  ; extends = extends P
  ; types   = types P
  ; X'      = B
  ; ε'      = ε' P ·̂ₑ ε₂
  ; typed   = (subC (proj₁ (typed P)) (subtype P ‼ₛ ⊩≾̂ₑ-refl) ⨟ rename-c r DN) ,
              cong₂ _⨟_ (proj₂ (typed P))
                        (trans (∥rename-c∥ r DN) (cong (renᶜ (ext (wkₛ e))) eN))
  ; subtype = p₀
  ; grade   = transᵣ (regroup (grade P)) (map-mono q₀)
  }
  where r = ext-lock (⊆-ext (extends P)) (grade P) ⇑ʳ

-- passage of time

preservation {Σ = Σ} {ε = ε} T (D , eD) (DELAY {τ}) with invC≡ D eD
... | _ , (A , ε₁ , refl , (DM , eM)) , (p₀ ‼ₛ q₀) = record
  { Σ'      = Σ ⟨⟩ˢ
  ; extends = ⊆-lock ⊆-refl
  ; types   = T ⟨⟩ˢ
  ; X'      = A
  ; ε'      = ε₁
  ; typed   = DM , eM
  ; subtype = p₀
  ; grade   = transᵣ (monoᵣ (transᵣ (eqᵣ ≡̂ᵣ-identityˡ) dur) ⊩≾̂ᵣ-refl)
                     (transᵣ ∣·∣ (map-mono q₀))
  }
  where
    dur : ⊤ᴴ ⊩ rconst (of-durʳ τ) ≾̂ᵣ ∣ econst (of-durᵉ τ) ∣̂ᵉ
    dur = eqᵣ (≡̂ᵣ-trans (≡̂ᵣ-const (≃ᵣ-sym map-of-durᵉ)) (≡̂ᵣ-sym ≡̂ᵣ-map-const))

-- effect handling

preservation T (D , eD) HANDLE-RET with invC≡ D eD
... | _ , (A , B , ε₁ , ε₂ , refl , (DR , eR) , (DH , eH)) , q₀
    with invC≡ DR eR | invV≡ DH eH
... | _ , (A₃ , refl , (DV , eV)) , (p₃ ‼ₛ q₃)
    | _ , (A₄ , B₄ , ε₄ , ε₄' , refl , (DN , eN) , _) , ((pA ‼ₛ pε) ⇛ₛ (pB ‼ₛ pε')) =
  stay T (sub-c here (subV DV (<:̂ᵛ-trans p₃ pA)) (rename-c r DN))
       (trans (∥sub-c∥ here (subV DV (<:̂ᵛ-trans p₃ pA)) (rename-c r DN))
              (cong₂ (subᶜ 0) eV (trans (∥rename-c∥ r DN)
                                        (trans (ren-idᶜ (ext-id (λ i → refl)) ∥ DN ∥ᶜ) eN))))
       (<:̂ᶜ-trans (pB ‼ₛ transₑ pε' (≾-·ˡ q₃)) q₀)
  where r = lock-remove (û≾∣∣ (transₑ q₃ pε)) ⇑ʳ

preservation {Σ = Σ} T (D , eD) (HANDLE-OP {op} {V} {M} {N} {H}) with invC≡ D eD
... | _ , (A , B , ε₁ , ε₂ , refl , (DP , eP) , (DH , eH)) , q₀
    with invC≡ DP eP | invV≡ DH eH
... | _ , (A₃ , ε₃ , refl , (DV , eV) , (DM , eM)) , (p₃ ‼ₛ q₃)
    | _ , (A₄ , B₄ , ε₄ , ε₄' , refl , (DN , eN) , (DHs , eHs)) , ((pA ‼ₛ pε) ⇛ₛ (pB ‼ₛ pε')) =
  stay T (box (rconst (mapᵉ (op-grade op)))
              (lam (handle subC DM (<:̂ᵛ-trans p₃ pA ‼ₛ ⊩≾̂ₑ-refl) `with proj₁ H')) Mop)
       (cong₂ box (cong lam (cong₂ handle_`with_ eM
                                   (trans (proj₂ H')
                                          (cong₂ (λ a b → renᵛ suc (handler a b)) eN
                                                 (fun-ext eHs)))))
                  eMop)
       (<:̂ᶜ-trans (pB ‼ₛ transₑ (eqₑ (≡̂ₑ-sym ≡̂ₑ-assoc)) (monoₑ q₃ pε')) q₀)
  where
    e₀ : Ext ⊤ᴴ (ctx Σ) (ctx Σ ⟨ rconst (mapᵉ (op-grade op)) ⟩ ∷ ⌜ arity op ⌝ᵍ)
             (rconst (mapᵉ (op-grade op)))
    e₀ = wk-ext lock-ext
    le : ⊤ᴴ ⊩ rconst (mapᵉ (op-grade op)) ·̂ᵣ ∣ ε₃ ∣̂ᵉ ≾̂ᵣ ∣ ε₄ ∣̂ᵉ
    le = transᵣ (monoᵣ ∣const∣ ⊩≾̂ᵣ-refl) (transᵣ ∣·∣ (map-mono (transₑ q₃ pε)))
    H' = retype {ε₁ = ε₃} e₀ le DN DHs
    Cl = instantiate-clause (ε₃ ·̂ₑ ε₄') (DHs op)
    r : Ren ⊤ᴴ (ctx Σ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                 ∷ [ rconst (mapᵉ (op-grade op)) ] (⌜ arity op ⌝ᵍ ⇒ B₄ ‼ (ε₃ ·̂ₑ ε₄')))
               (ctx Σ ∷ ⌜ param op ⌝ᵍ
                 ∷ [ rconst (mapᵉ (op-grade op)) ] (⌜ arity op ⌝ᵍ ⇒ B₄ ‼ (ε₃ ·̂ₑ ε₄')))
    r = (lock-remove topᵣ ⇑ʳ) ⇑ʳ
    Mop = sub-c (there∷ here) DV (rename-c r Cl)
    eMop : ∥ Mop ∥ᶜ ≡ H op [ V ]₁
    eMop =
      trans (∥sub-c∥ (there∷ here) DV (rename-c r Cl))
            (cong₂ (subᶜ 1) eV
                   (trans (∥rename-c∥ r Cl)
                          (trans (ren-idᶜ (ext-id (ext-id (λ i → refl))) ∥ Cl ∥ᶜ)
                                 (trans (cong eraseᶜ (⌊instantiate-clause⌋ (ε₃ ·̂ₑ ε₄') (DHs op)))
                                        (trans (erase-substᶜ ⌊ DHs op ⌋ᶜ _) (eHs op))))))

preservation {Σ = Σ} T (D , eD) (HANDLE-STEP {e = e} s) with invC≡ D eD
... | _ , (A , B , ε₁ , ε₂ , refl , (DM , eM) , (DH , eH)) , (p₀ ‼ₛ q₀)
    with handler-form (canon-⇛ (ctx-box Σ) DH) | preservation T (DM , eM) s
... | N , H , cH | P with invV≡ DH cH
... | _ , (A₄ , B₄ , ε₄ , ε₄' , refl , (DN , eN) , (DHs , eHs)) , ((pA ‼ₛ pε) ⇛ₛ (pB ‼ₛ pε')) =
  record
  { Σ'      = Σ' P
  ; extends = extends P
  ; types   = types P
  ; X'      = B₄
  ; ε'      = ε' P ·̂ₑ ε₄'
  ; typed   = handle subC (proj₁ (typed P)) (<:̂ᵛ-trans (subtype P) pA ‼ₛ ⊩≾̂ₑ-refl)
                `with proj₁ H' ,
              cong₂ handle_`with_ (proj₂ (typed P))
                    (trans (proj₂ H')
                           (cong (renᵛ (wkₛ e))
                                 (trans (cong₂ handler eN (fun-ext eHs)) (trans (sym cH) eH))))
  ; subtype = <:̂ᵛ-trans pB p₀
  ; grade   = transᵣ (regroup (grade P))
                     (map-mono (transₑ (monoₑ ⊩≾̂ₑ-refl pε') q₀))
  }
  where H' = retype (⊆-ext (extends P)) (transᵣ (grade P) (map-mono pε)) DN DHs

-- resources

preservation {Σ = Σ} T (D , eD) BOX with invC≡ D eD
... | _ , (ρ , A , (DV , eV) , (DN , eN)) , (p₀ ‼ₛ q₀) = record
  { Σ'      = Σ ∷[ ρ ] A
  ; extends = ⊆-res ⊆-refl
  ; types   = T ∷ᵗ (DV , eV)
  ; X'      = _
  ; ε'      = _
  ; typed   = DN , eN
  ; subtype = p₀
  ; grade   = transᵣ (eqᵣ ≡̂ᵣ-identityˡ) (map-mono q₀)
  }

preservation T (D , eD) UNBOX with invC≡ D eD
... | _ , (ρ₀ , A₀ , ρ' , A , x , refl , p , q , (DN , eN)) , q₀ =
  stay T (sub-c here (subV (proj₁ L) q) DN)
       (trans (∥sub-c∥ here (subV (proj₁ L) q) DN) (cong₂ (subᶜ 0) (proj₂ L) eN)) q₀
  where L = lookup-typed T x p

------------------------------------------------------------------------
-- Progress

private

  step : ∀ {n m} {S : State n} {S' : State m} {e : S ≤ₛ S'} {M M'}
       → ⟨ S ∣ M ⟩↝[ e ]⟨ S' ∣ M' ⟩ → Final M ⊎ Steps S M
  step s = inj₂ (_ , _ , _ , _ , s)

progress : ∀ {n} {S : State n} {Σ : StateTyping S} {M C}
         → ctx Σ ⊢ᶜ M ⦂ C → Final M ⊎ Steps S M

progress {M = return V}       _ = inj₁ (is-return V)
progress {M = perform op V M} _ = inj₁ (is-perform op V M)

progress {M = M ⨟ N} (D , eD) with invC≡ D eD
... | _ , (A , B , ε₁ , ε₂ , refl , (DM , eM) , _) , _ with progress (DM , eM)
... | inj₁ (is-return V)          = step SEQ-RET
... | inj₁ (is-perform op V M')   = step SEQ-OP
... | inj₂ (_ , _ , _ , _ , s)    = step (SEQ-STEP s)

progress {Σ = Σ} {M = V · W} (D , eD) with invC≡ D eD
... | _ , (A , (DV , eV) , _) , _ with subst LamView eV (canon-⇒ (ctx-box Σ) DV)
... | is-lam M = step APP

progress {Σ = Σ} {M = match V `in M} (D , eD) with invC≡ D eD
... | _ , (A , B , (DV , eV) , _) , _ with subst PairView eV (canon-× (ctx-box Σ) DV)
... | is-pair V₁ V₂ = step MATCH

progress {Σ = Σ} {M = absurd V} (D , eD) with invC≡ D eD
... | _ , (DV , eV) , _ = ⊥-elim (canon-Empty (ctx-box Σ) DV)

progress {Σ = Σ} {M = if V `then M `else N} (D , eD) with invC≡ D eD
... | _ , ((DV , eV) , _) , _ with subst BoolView eV (canon-Bool (ctx-box Σ) DV)
... | is-true       = step IF-TRUE
... | is-false      = step IF-FALSE
... | is-cmp ⋈ W W' = step CMP

progress {Σ = Σ} {M = caseℕ V `zero M `succ N} (D , eD) with invC≡ D eD
... | _ , ((DV , eV) , _) , _ with subst NatView eV (canon-Nat (ctx-box Σ) DV)
... | is-zero   = step CASEℕ-ZERO
... | is-succ W = step CASEℕ-SUCC

progress {Σ = Σ} {M = case+ V `inl M `inr N} (D , eD) with invC≡ D eD
... | _ , (A , B , (DV , eV) , _) , _ with subst SumView eV (canon-+ (ctx-box Σ) DV)
... | is-inl W = step CASE-INL
... | is-inr W = step CASE-INR

progress {Σ = Σ} {M = caseL V `nil M `cons N} (D , eD) with invC≡ D eD
... | _ , (A , (DV , eV) , _) , _ with subst ListView eV (canon-List (ctx-box Σ) DV)
... | is-nil       = step CASEL-NIL
... | is-cons W W' = step CASEL-CONS

progress {Σ = Σ} {M = recℕ V M N} (D , eD) with invC≡ D eD
... | _ , (B , ε , refl , (DV , eV) , _) , _ with subst NatView eV (canon-Nat (ctx-box Σ) DV)
... | is-zero   = step RECℕ-ZERO
... | is-succ W = step RECℕ-SUCC

progress {Σ = Σ} {M = recL V M N} (D , eD) with invC≡ D eD
... | _ , (A , B , ε , refl , (DV , eV) , _) , _ with subst ListView eV (canon-List (ctx-box Σ) DV)
... | is-nil       = step RECL-NIL
... | is-cons W W' = step RECL-CONS

progress {M = delay τ M} _ = step DELAY

progress {Σ = Σ} {M = handle M `with V} (D , eD) with invC≡ D eD
... | _ , (A , B , ε₁ , ε₂ , refl , (DM , eM) , (DH , eH)) , _
    with progress (DM , eM) | subst HandlerView eH (canon-⇛ (ctx-box Σ) DH)
... | inj₁ (is-return W)        | is-handler N H = step HANDLE-RET
... | inj₁ (is-perform op W M') | is-handler N H = step HANDLE-OP
... | inj₂ (_ , _ , _ , _ , s)  | _              = step (HANDLE-STEP s)

progress {M = unbox V N} (D , eD) with invC≡ D eD
... | _ , (ρ₀ , A₀ , ρ' , A , x , refl , _) , _ = step UNBOX

progress {M = box V N} _ = step BOX

------------------------------------------------------------------------
-- Type safety

type-safety : ∀ {n} {S : State n} {Σ : StateTyping S} {M X ε}
            → Types Σ → ctx Σ ⊢ᶜ M ⦂ X ‼ ε
            → Final M
              ⊎ Σ[ m ∈ ℕ ] Σ[ S' ∈ State m ] Σ[ M' ∈ RunC m ] Σ[ e ∈ S ≤ₛ S' ]
                  ⟨ S ∣ M ⟩↝[ e ]⟨ S' ∣ M' ⟩ × Preserved e Σ M' X ε
type-safety T D with progress D
... | inj₁ f                     = inj₁ f
... | inj₂ (_ , _ , _ , e , s)   = inj₂ (_ , _ , _ , e , s , preservation T D s)
