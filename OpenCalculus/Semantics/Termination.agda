------------------------------------------------------------------
-- Termination of the reduction                                 --
--                                                              --
-- A typed term, its variables replaced by reducible values, is --
-- reducible (`fund-v`, `fund-c`); a term typed in the empty    --
-- context, run from the empty state, reduces in finitely many  --
-- steps to a returned value or an operation call               --
-- (`termination`).                                             --
------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool.Base using () renaming (true to tt𝔹; false to ff𝔹)

open import Grades.Base
open import Language.Spec
open import Language.Operations
open import Language.Comparisons using (Cmp; holds)

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Semantics.Termination (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OpenCalculus.Syntax.Grades            S
open import OpenCalculus.Syntax.Types             S
open import OpenCalculus.Syntax.Contexts          S
open import OpenCalculus.Syntax.ContextsLemmas    S
open import OpenCalculus.Hypotheses               S
open import OpenCalculus.Typing                   S
open import OpenCalculus.Typing.GradeSubstitution S using (clause-ctx)
open import OpenCalculus.Typing.Renaming          S using (∥_∥ᵛ; ∥_∥ᶜ)
open import OpenCalculus.Typing.Inversion         S using (is-true; is-false; is-cmp)
open import OpenCalculus.Typing.ScopeClosed       S
open import OpenCalculus.Syntax.Run               S
open import OpenCalculus.Syntax.Run.Substitution  S
open import OpenCalculus.Semantics.States         S
open import OpenCalculus.Semantics.Reduction      S
open import OpenCalculus.Semantics.Termination.Reducibility S

------------------------------------------------------------------------
-- Substitution lemmas

private

  -- a value for the variable bound last

  _∙_ : ∀ {n m} → (Fin n → RunV m) → RunV m → Fin (suc n) → RunV m
  (σ ∙ W) zero    = W
  (σ ∙ W) (suc i) = σ i

  infixl 30 _∙_

  psub-wk : ∀ {n m} {σ : Fin (suc n) → RunV m} {f : Fin n → Fin m}
          → (∀ i → σ (suc i) ≡ var (f i)) → (V : RunV n) → psubᵛ σ (wkᵛ V) ≡ renᵛ f V
  psub-wk p V = trans (psub-renᵛ (λ i → refl) V) (psub-varᵛ p V)

  -- the substitution at depth 0, 1 and 2 after a lifted one

  sub₀ : ∀ {n m} → (σ : Fin n → RunV m) → (W : RunV m) → (M : RunC (suc n))
       → psubᶜ (exts σ) M [ W ]₀ ≡ psubᶜ (σ ∙ W) M
  sub₀ σ W M =
    trans (sub-psubᶜ 0 W (psubᶜ (exts σ) M)) (trans (psub-psubᶜ (λ i → refl) M) (psub-congᶜ pw M))
    where
      pw : ∀ i → psubᵛ (subVar 0 W) (exts σ i) ≡ (σ ∙ W) i
      pw zero    = refl
      pw (suc i) = trans (psub-wk (λ j → refl) (σ i)) (ren-idᵛ (λ j → refl) (σ i))

  sub₁ : ∀ {n m} → (σ : Fin n → RunV m) → (V : RunV m) → (M : RunC (suc (suc n)))
       → psubᶜ (exts (exts σ)) M [ V ]₁ ≡ psubᶜ (exts (σ ∙ V)) M
  sub₁ σ V M =
    trans (sub-psubᶜ 1 V (psubᶜ (exts (exts σ)) M))
          (trans (psub-psubᶜ (λ i → refl) M) (psub-congᶜ pw M))
    where
      pw : ∀ i → psubᵛ (subVar 1 V) (exts (exts σ) i) ≡ exts (σ ∙ V) i
      pw zero          = refl
      pw (suc zero)    = refl
      pw (suc (suc i)) = trans (psub-renᵛ (λ j → refl) (wkᵛ (σ i))) (psub-wk (λ j → refl) (σ i))

  sub₂ : ∀ {n m} → (σ : Fin n → RunV m) → (V : RunV m) → (M : RunC (suc (suc (suc n))))
       → psubᶜ (exts (exts (exts σ))) M [ V ]₂ ≡ psubᶜ (exts (exts (σ ∙ V))) M
  sub₂ σ V M =
    trans (sub-psubᶜ 2 V (psubᶜ (exts (exts (exts σ))) M))
          (trans (psub-psubᶜ (λ i → refl) M) (psub-congᶜ pw M))
    where
      pw : ∀ i → psubᵛ (subVar 2 V) (exts (exts (exts σ)) i) ≡ exts (exts (σ ∙ V)) i
      pw zero                = refl
      pw (suc zero)          = refl
      pw (suc (suc zero))    = refl
      pw (suc (suc (suc i))) =
        trans (psub-renᵛ (λ j → refl) (wkᵛ (wkᵛ (σ i))))
              (trans (psub-renᵛ (λ j → refl) (wkᵛ (σ i)))
                     (trans (psub-wk (λ j → refl) (σ i))
                            (sym (ren-fuseᵛ (λ j → refl) (σ i)))))

  -- renaming after a lifted substitution

  ren-exts₁ : ∀ {n m k} → (f : Fin m → Fin k) → (σ : Fin n → RunV m) → (M : RunC (suc n))
            → renᶜ (ext f) (psubᶜ (exts σ) M) ≡ psubᶜ (exts (λ i → renᵛ f (σ i))) M
  ren-exts₁ f σ M = ren-psubᶜ (ren-exts (λ i → refl)) M

  ren-exts₂ : ∀ {n m k} → (f : Fin m → Fin k) → (σ : Fin n → RunV m) → (M : RunC (suc (suc n)))
            → renᶜ (ext (ext f)) (psubᶜ (exts (exts σ)) M)
              ≡ psubᶜ (exts (exts (λ i → renᵛ f (σ i)))) M
  ren-exts₂ f σ M = ren-psubᶜ (ren-exts (ren-exts (λ i → refl))) M

  -- the continuation of a binder, at an extension and a value

  bind : ∀ {n m k} → (f : Fin m → Fin k) → (σ : Fin n → RunV m) → (W : RunV k)
       → (M : RunC (suc n))
       → renᶜ (ext f) (psubᶜ (exts σ) M) [ W ]₀ ≡ psubᶜ ((λ i → renᵛ f (σ i)) ∙ W) M
  bind f σ W M = trans (cong (_[ W ]₀) (ren-exts₁ f σ M)) (sub₀ _ W M)

------------------------------------------------------------------------
-- Environments: reducible values for the variables of a context
-- without definitions

record Env {Θ n m} (Γ : OCtx Θ n) (S : State m) (σ : Fin n → RunV m) : Set where
  constructor env
  field
    at     : ∀ i → VRed (shapeᵛ (lookup-ty Γ i)) S (σ i)
    nodefs : defs Γ ≡ ∅ᵖ

open Env

private

  env-mono : ∀ {Θ n m k} {Γ : OCtx Θ n} {S : State m} {S' : State k} {σ}
           → Env Γ S σ → (e : S ≤ₛ S') → Env Γ S' (λ i → renᵛ (wkₛ e) (σ i))
  at (env-mono {Γ = Γ} {σ = σ} r e) i = VRed-mono (shapeᵛ (lookup-ty Γ i)) e (σ i) (at r i)
  nodefs (env-mono r e) = nodefs r

  ⟨⟩ᵉ : ∀ {Θ n m} {Γ : OCtx Θ n} {ρ : RExp Θ} {S : State m} {σ}
      → Env Γ S σ → Env (Γ ⟨ ρ ⟩) S σ
  at (⟨⟩ᵉ r) = at r
  nodefs (⟨⟩ᵉ r) = nodefs r

  env-∙ : ∀ {Θ n m} {Γ : OCtx Θ n} {A : OVType Θ} {S : State m} {σ W}
        → Env Γ S σ → VRed (shapeᵛ A) S W → Env (Γ ∷ A) S (σ ∙ W)
  at (env-∙ r w) zero    = w
  at (env-∙ r w) (suc i) = at r i
  nodefs (env-∙ r w) = nodefs r

  -- views of the reducible values of a shape

  data LamRed {n} (A B : Shape) (S : State n) : RunV n → Set where
    lam-red : ∀ {M} → VRed (A ⇒ˢ B) S (lam M) → LamRed A B S (lam M)

  lam-red? : ∀ {n A B} {S : State n} V → VRed (A ⇒ˢ B) S V → LamRed A B S V
  lam-red? (lam M) r = lam-red r

  data HandlerRed {n} (A B : Shape) (S : State n) : RunV n → Set where
    handler-red : ∀ {N H} → VRed (A ⇛ˢ B) S (handler N H) → HandlerRed A B S (handler N H)

  handler-red? : ∀ {n A B} {S : State n} V → VRed (A ⇛ˢ B) S V → HandlerRed A B S V
  handler-red? (handler N H) r = handler-red r

  data PairRed {n} (A B : Shape) (S : State n) : RunV n → Set where
    pair-red : ∀ {V W} → VRed A S V → VRed B S W → PairRed A B S ⦉ V , W ⦊

  pair-red? : ∀ {n A B} {S : State n} V → VRed (A ×ˢ B) S V → PairRed A B S V
  pair-red? ⦉ V , W ⦊ (r , r') = pair-red r r'

  data SumRed {n} (A B : Shape) (S : State n) : RunV n → Set where
    inl-red : ∀ {V} → VRed A S V → SumRed A B S (inl V)
    inr-red : ∀ {V} → VRed B S V → SumRed A B S (inr V)

  sum-red? : ∀ {n A B} {S : State n} V → VRed (A +ˢ B) S V → SumRed A B S V
  sum-red? (inl V) r = inl-red r
  sum-red? (inr V) r = inr-red r

  data ListRed {n} (A : Shape) (S : State n) : RunV n → Set where
    nil-red  : ListRed A S nil
    cons-red : ∀ {V W} → VRed A S V → VRed (listˢ A) S W → ListRed A S (cons V W)

  list-red? : ∀ {n A} {S : State n} V → VRed (listˢ A) S V → ListRed A S V
  list-red? nil        r        = nil-red
  list-red? (cons V W) (r , r') = cons-red r r'

  data NatRed {n} (S : State n) : RunV n → Set where
    zero-red : NatRed S zero
    succ-red : ∀ {V} → VRed natˢ S V → NatRed S (succ V)

  nat-red? : ∀ {n} {S : State n} V → VRed natˢ S V → NatRed S V
  nat-red? zero     r = zero-red
  nat-red? (succ V) r = succ-red r

  data BoxRed {n} (A : Shape) (S : State n) : RunV n → Set where
    box-red : ∀ {i} → VRed A S (lookupₛ S i) → BoxRed A S (var i)

  box-red? : ∀ {n A} {S : State n} V → VRed (□ˢ A) S V → BoxRed A S V
  box-red? (var i) r = box-red r

  -- a decided comparison

  decided : ∀ {n} → (⋈ : Cmp) → (V W : RunV n) → decide ⋈ V W ≡ true ⊎ decide ⋈ V W ≡ false
  decided ⋈ V W with holds ⋈ (compareᴰ (datum V) (datum W))
  ... | tt𝔹 = inj₁ refl
  ... | ff𝔹 = inj₂ refl

------------------------------------------------------------------------
-- The fundamental lemma

mutual

  fund-v : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ} {S : State m} {σ}
         → (D : Q ∣ Γ ⊢V⦂ A) → Env Γ S σ → VRed (shapeᵛ A) S (psubᵛ σ ∥ D ∥ᵛ)
  fund-v {S = S} {σ} (var x p) r =
    subst (λ T → VRed (shapeᵛ T) S (σ (var-pos x))) (var-pos-ty x) (at r (var-pos x))
  fund-v (const B c)     r = tt
  fund-v ⋆               r = tt
  fund-v true            r = is-true
  fund-v false           r = is-false
  fund-v zero            r = tt
  fund-v (succ V)        r = fund-v V r
  fund-v ⦉ V , W ⦊        r = fund-v V r , fund-v W r
  fund-v (inl V)         r = fund-v V r
  fund-v (inr V)         r = fund-v V r
  fund-v nil             r = tt
  fund-v (cons V W)      r = fund-v V r , fund-v W r
  fund-v (cmp ⋈ V W et)  r = is-cmp ⋈ _ _
  fund-v {σ = σ} (lam {C = C} M) r {S' = S'} e W w =
    subst (CRed (VRed (shapeᶜ C)) S') (sym (bind (wkₛ e) σ W ∥ M ∥ᶜ))
          (fund-c M (env-∙ (env-mono r e) w))
  fund-v {Γ = Γ} {S = S₀} {σ} (handler {A} {B} N H) r e M c =
    cred-handle {A = shapeᵛ A} {B = shapeᵛ B} hyp-ret hyp-op e c
    where
      hyp-ret : ∀ {m} {S' : State m} (e : S₀ ≤ₛ S') V → VRed (shapeᵛ A) S' V
              → CRed (VRed (shapeᵛ B)) S' (renᶜ (ext (wkₛ e)) (psubᶜ (exts σ) ∥ N ∥ᶜ) [ V ]₀)
      hyp-ret {S' = S'} e V v =
        subst (CRed (VRed (shapeᵛ B)) S') (sym (bind (wkₛ e) σ V ∥ N ∥ᶜ))
              (fund-c N (env-∙ (⟨⟩ᵉ (env-mono r e)) v))

      hyp-op : ∀ op {m} {S' : State m} (e : S₀ ≤ₛ S') V kv
             → VRedᵍ (param op) S' V
             → VRed (shapeᵍ (arity op) ⇒ˢ shapeᵛ B) (S' ∷ₛ kv) (wkᵛ kv)
             → CRed (VRed (shapeᵛ B)) (S' ∷ₛ kv)
                    (renᶜ (ext (ext (wkₛ e))) (psubᶜ (exts (exts σ)) ∥ H op ∥ᶜ) [ V ]₁)
      hyp-op op {S' = S'} e V kv v k =
        subst₂ (λ s X → CRed (VRed s) (S' ∷ₛ kv) X)
               (wkᵉ-shapeᵛ B)
               (sym (trans (cong (_[ V ]₁) (ren-exts₂ (wkₛ e) σ ∥ H op ∥ᶜ)) (sub₁ _ V ∥ H op ∥ᶜ)))
               (fund-c (H op) env-cl)
        where
          env-cl : Env (clause-ctx Γ B op) (S' ∷ₛ kv)
                       (exts ((λ i → renᵛ (wkₛ e) (σ i)) ∙ V))
          at env-cl zero          =
            subst (λ s → VRed s (S' ∷ₛ kv) (wkᵛ kv))
                  (sym (cong₂ _⇒ˢ_ (shape-⌜⌝ (arity op)) (wkᵉ-shapeᵛ B))) k
          at env-cl (suc zero)    =
            subst (λ s → VRed s (S' ∷ₛ kv) (wkᵛ V)) (sym (shape-⌜⌝ (param op)))
                  (ground-VRed (param op) (wkᵛ V) (VRedᵍ-mono (param op) res₁ V v))
          at env-cl (suc (suc i)) =
            subst₂ (λ s X → VRed s (S' ∷ₛ kv) X)
                   (trans (sym (wkᵉ-shapeᵛ (lookup-ty Γ i)))
                          (cong shapeᵛ (sym (lookup-ty-wkᵉ Γ i))))
                   (sym (ren-⨾ᵛ e (res₁ {V = kv}) (σ i)))
                   (at (env-mono r (e ⨾ₛ res₁ {V = kv})) i)
          nodefs env-cl = trans (defs-wkᵉ Γ) (nodefs r)
  fund-v (def f δ h e)   r = ⊥-elim (∅ᵖ-∌ (subst (_ ∈ᵖ[ _ ]_) (nodefs r) f))
  fund-v (annᵛ A V)      r = fund-v V r
  fund-v {S = S} (subV V p) r = subst (λ s → VRed s S _) (<:-shapeᵛ p) (fund-v V r)

  fund-c : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ} {S : State m} {σ}
         → (D : Q ∣ Γ ⊢C⦂ C) → Env Γ S σ → CRed (VRed (shapeᶜ C)) S (psubᶜ σ ∥ D ∥ᶜ)

  fund-c (return V) r = cred-ret done (fund-v V r)

  fund-c {σ = σ} (_⨟_ {A} {B} M N) r =
    cred-seq {A = shapeᵛ A} (fund-c M r)
             (λ {_} {S'} e W w → subst (CRed (VRed (shapeᵛ B)) S') (sym (bind (wkₛ e) σ W ∥ N ∥ᶜ))
                                       (fund-c N (env-∙ (⟨⟩ᵉ (env-mono r e)) w)))

  fund-c {S = S} {σ} (_·_ {C = C} V W) r
    with psubᵛ σ ∥ V ∥ᵛ | lam-red? (psubᵛ σ ∥ V ∥ᵛ) (fund-v V r)
  ... | _ | lam-red {M} f =
    cred-back (APP ▸ done)
              (subst (λ X → CRed (VRed (shapeᶜ C)) S (X [ psubᵛ σ ∥ W ∥ᵛ ]₀))
                     (ren-idᶜ (ext-id (λ i → refl)) M)
                     (f ≤ₛ-refl _ (fund-v W r)))

  fund-c {S = S} {σ} (match_`in_ {C = C} V M) r
    with psubᵛ σ ∥ V ∥ᵛ | pair-red? (psubᵛ σ ∥ V ∥ᵛ) (fund-v V r)
  ... | _ | pair-red {V₁} {V₂} r₁ r₂ =
    cred-back (MATCH ▸ done)
              (subst (CRed (VRed (shapeᶜ C)) S)
                     (sym (trans (cong (_[ V₂ ]₀) (sub₁ σ V₁ ∥ M ∥ᶜ)) (sub₀ _ V₂ ∥ M ∥ᶜ)))
                     (fund-c M (env-∙ (env-∙ r r₁) r₂)))

  fund-c (absurd V) r = ⊥-elim (fund-v V r)

  fund-c {S = S} {σ} (if V `then M `else N) r
    with psubᵛ σ ∥ V ∥ᵛ | fund-v V r
  ... | _ | is-true          = cred-back (IF-TRUE ▸ done) (fund-c M r)
  ... | _ | is-false         = cred-back (IF-FALSE ▸ done) (fund-c N r)
  ... | _ | is-cmp ⋈ W₁ W₂ with decided ⋈ W₁ W₂
  ...   | inj₁ eq =
    cred-back (CMP ▸ subst (λ X → ⟨ S ∣ if X `then psubᶜ σ ∥ M ∥ᶜ `else psubᶜ σ ∥ N ∥ᶜ ⟩↝*⟨ S ∣ psubᶜ σ ∥ M ∥ᶜ ⟩)
                           (sym eq) (IF-TRUE ▸ done))
              (fund-c M r)
  ...   | inj₂ eq =
    cred-back (CMP ▸ subst (λ X → ⟨ S ∣ if X `then psubᶜ σ ∥ M ∥ᶜ `else psubᶜ σ ∥ N ∥ᶜ ⟩↝*⟨ S ∣ psubᶜ σ ∥ N ∥ᶜ ⟩)
                           (sym eq) (IF-FALSE ▸ done))
              (fund-c N r)

  fund-c {S = S} {σ} (caseℕ_`zero_`succ_ {C = C} V M N) r
    with psubᵛ σ ∥ V ∥ᵛ | nat-red? (psubᵛ σ ∥ V ∥ᵛ) (fund-v V r)
  ... | _ | zero-red         = cred-back (CASEℕ-ZERO ▸ done) (fund-c M r)
  ... | _ | succ-red {W} w   =
    cred-back (CASEℕ-SUCC ▸ done)
              (subst (CRed (VRed (shapeᶜ C)) S) (sym (sub₀ σ W ∥ N ∥ᶜ)) (fund-c N (env-∙ r w)))

  fund-c {S = S} {σ} (case+_`inl_`inr_ {C = C} V M N) r
    with psubᵛ σ ∥ V ∥ᵛ | sum-red? (psubᵛ σ ∥ V ∥ᵛ) (fund-v V r)
  ... | _ | inl-red {W} w =
    cred-back (CASE-INL ▸ done)
              (subst (CRed (VRed (shapeᶜ C)) S) (sym (sub₀ σ W ∥ M ∥ᶜ)) (fund-c M (env-∙ r w)))
  ... | _ | inr-red {W} w =
    cred-back (CASE-INR ▸ done)
              (subst (CRed (VRed (shapeᶜ C)) S) (sym (sub₀ σ W ∥ N ∥ᶜ)) (fund-c N (env-∙ r w)))

  fund-c {S = S} {σ} (caseL_`nil_`cons_ {C = C} V M N) r
    with psubᵛ σ ∥ V ∥ᵛ | list-red? (psubᵛ σ ∥ V ∥ᵛ) (fund-v V r)
  ... | _ | nil-red = cred-back (CASEL-NIL ▸ done) (fund-c M r)
  ... | _ | cons-red {W₁} {W₂} w₁ w₂ =
    cred-back (CASEL-CONS ▸ done)
              (subst (CRed (VRed (shapeᶜ C)) S)
                     (sym (trans (cong (_[ W₂ ]₀) (sub₁ σ W₁ ∥ N ∥ᶜ)) (sub₀ _ W₂ ∥ N ∥ᶜ)))
                     (fund-c N (env-∙ (env-∙ r w₁) w₂)))

  fund-c {S = S} {σ} (recℕ {B = B} V M N p) r = rec (psubᵛ σ ∥ V ∥ᵛ) (fund-v V r)
    where
      M' = psubᶜ σ ∥ M ∥ᶜ
      N' = psubᶜ (exts (exts σ)) ∥ N ∥ᶜ

      rec : ∀ W → VRed natˢ S W → CRed (VRed (shapeᵛ B)) S (recℕ W M' N')
      rec W w with nat-red? W w
      ... | zero-red        = cred-back (RECℕ-ZERO ▸ done) (fund-c M r)
      ... | succ-red {W'} w' =
        cred-back (RECℕ-SUCC ▸ done)
          (cred-seq {A = shapeᵛ B} (rec W' w')
                    (λ {_} {S'} e X x →
                       subst (CRed (VRed (shapeᵛ B)) S')
                             (sym (trans (cong (λ Y → renᶜ (ext (wkₛ e)) Y [ X ]₀)
                                               (sub₁ σ W' ∥ N ∥ᶜ))
                                         (bind (wkₛ e) (σ ∙ W') X ∥ N ∥ᶜ)))
                             (fund-c N (env-∙ (env-mono (⟨⟩ᵉ (env-∙ (⟨⟩ᵉ r) w')) e) x))))

  fund-c {S = S} {σ} (recL {A = A} {B = B} V M N p) r = rec (psubᵛ σ ∥ V ∥ᵛ) (fund-v V r)
    where
      M' = psubᶜ σ ∥ M ∥ᶜ
      N' = psubᶜ (exts (exts (exts σ))) ∥ N ∥ᶜ

      rec : ∀ W → VRed (listˢ (shapeᵛ A)) S W → CRed (VRed (shapeᵛ B)) S (recL W M' N')
      rec W w with list-red? W w
      ... | nil-red = cred-back (RECL-NIL ▸ done) (fund-c M r)
      ... | cons-red {W₁} {W₂} w₁ w₂ =
        cred-back (RECL-CONS ▸ done)
          (cred-seq {A = shapeᵛ B} (rec W₂ w₂)
                    (λ {_} {S'} e X x →
                       subst (CRed (VRed (shapeᵛ B)) S')
                             (sym (trans (cong (λ Y → renᶜ (ext (wkₛ e)) Y [ X ]₀)
                                               (trans (cong (_[ W₂ ]₁) (sub₂ σ W₁ ∥ N ∥ᶜ))
                                                      (sub₁ (σ ∙ W₁) W₂ ∥ N ∥ᶜ)))
                                         (bind (wkₛ e) (σ ∙ W₁ ∙ W₂) X ∥ N ∥ᶜ)))
                             (fund-c N (env-∙ (env-mono (⟨⟩ᵉ (env-∙ (env-∙ (⟨⟩ᵉ r) w₁) w₂)) e) x))))

  fund-c {S = S} {σ} (perform {A = A} op V M) r =
    cred-op done
            (VRed-ground (param op) (psubᵛ σ ∥ V ∥ᵛ)
               (subst (λ s → VRed s S (psubᵛ σ ∥ V ∥ᵛ)) (shape-⌜⌝ (param op)) (fund-v V r)))
            (λ {_} {S'} e W w →
               subst (CRed (VRed (shapeᵛ A)) S') (sym (bind (wkₛ e) σ W ∥ M ∥ᶜ))
                     (fund-c M (env-∙ (⟨⟩ᵉ (env-mono r e))
                                      (subst (λ s → VRed s S' W) (sym (shape-⌜⌝ (arity op)))
                                             (ground-VRed (arity op) W w)))))

  fund-c {Γ = Γ} {S = S} {σ} (delay τ M) r =
    cred-back (DELAY ▸ done) (fund-c M r')
    where
      r' : Env (Γ ⟨ rconst (of-durʳ τ) ⟩) (S ⟨ τ ⟩ₛ) σ
      at r' i = subst (VRed (shapeᵛ (lookup-ty Γ i)) (S ⟨ τ ⟩ₛ)) (ren-idᵛ (λ j → refl) (σ i))
                      (VRed-mono (shapeᵛ (lookup-ty Γ i)) (≤ₛ-lock ≤ₛ-refl) (σ i) (at r i))
      nodefs r' = nodefs r

  fund-c {S = S} {σ} (handle_`with_ {B = B} M V) r
    with psubᵛ σ ∥ V ∥ᵛ | handler-red? (psubᵛ σ ∥ V ∥ᵛ) (fund-v V r)
  ... | _ | handler-red {N} {H} f =
    subst (λ X → CRed (VRed (shapeᵛ B)) S (handle psubᶜ σ ∥ M ∥ᶜ `with X))
          (ren-idᵛ (λ i → refl) (handler N H))
          (f ≤ₛ-refl _ (fund-c M r))

  fund-c {Γ = Γ} {S = S} {σ} (unbox {C = C} x p q N) r
    with σ (var-pos x)
       | box-red? (σ (var-pos x))
                  (subst (λ T → VRed (shapeᵛ T) S (σ (var-pos x))) (var-pos-ty x) (at r (var-pos x)))
  ... | _ | box-red {j} w =
    cred-back (UNBOX ▸ done)
              (subst (CRed (VRed (shapeᶜ C)) S) (sym (sub₀ σ (lookupₛ S j) ∥ N ∥ᶜ))
                     (fund-c N (env-∙ r (subst (λ s → VRed s S (lookupₛ S j)) (<:-shapeᵛ q) w))))

  fund-c {Γ = Γ} {S = S} {σ} (box {A = A} ρ V N) r = cred-back (BOX ▸ done) (fund-c N r')
    where
      r' : Env (Γ ∷ [ ρ ] A) (S ∷ₛ psubᵛ σ ∥ V ∥ᵛ) (exts σ)
      at r' zero    = VRed-mono (shapeᵛ A) res₁ _ (fund-v V (⟨⟩ᵉ r))
      at r' (suc i) = VRed-mono (shapeᵛ (lookup-ty Γ i)) res₁ (σ i) (at r i)
      nodefs r' = nodefs r

  fund-c (annᶜ C M) r = fund-c M r
  fund-c {S = S} (subC M p) r = subst (λ s → CRed (VRed s) S _) (<:-shapeᶜ p) (fund-c M r)

------------------------------------------------------------------------
-- Termination

-- A run that finishes

Halts : ∀ {n} → State n → RunC n → Set
Halts S M = Σ[ m ∈ ℕ ] Σ[ S' ∈ State m ] Σ[ M' ∈ RunC m ] ⟨ S ∣ M ⟩↝*⟨ S' ∣ M' ⟩ × Final M'

halts : ∀ {P : ∀ {n} → State n → RunV n → Set} {n} {S : State n} {M} → CRed P S M → Halts S M
halts (cred-ret ms _)  = _ , _ , _ , ms , is-return _
halts (cred-op ms _ _) = _ , _ , _ , ms , is-perform _ _ _

termination : ∀ {M : RunC 0} {C : OCType ∅ˢ} → [] ⊢ᶜ M ⦂ C → Halts ∅ M
termination {M} (D , refl) =
  halts (subst (CRed _ ∅) (trans (psub-varᶜ {f = λ i → i} (λ ()) M) (ren-idᶜ (λ ()) M))
               (fund-c {σ = λ ()} D (env (λ ()) refl)))
