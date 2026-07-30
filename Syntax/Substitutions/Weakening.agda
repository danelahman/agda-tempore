------------------------------------------------------------------------
-- Substituting for a freshly weakened variable is the identity.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_; yes; no; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions.Weakening (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.RenActions    Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import Syntax.Renamings.Equivalence    Spec
open import Syntax.Renamings.Coherence      Spec
open import Syntax.Terms.Equivalence        Spec
open import Syntax.Terms.Transport          Spec
open import Syntax.Substitutions.Equivalence Spec
open import Syntax.Substitutions.Variables   Spec

-- SUBSTITUTING FOR A FRESHLY WEAKENED VARIABLE: THE VARIABLE CASE
--
-- The weakening's image never *is* the substituted variable, so a variable comes
-- back unchanged. Which of `sub-var-r`/`sub-var-l` applies depends on whether it
-- came from the suffix or the prefix, and `∈-++ᶜ-split` decides that.

sub-wk-var-r : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ} → (z : A ∈[ ρ ] Θ)
             → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
             → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
             → castᵛ (castOf {Γ} {B} Θ)
                 ((V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                            (var f (∈-++ᶜʳ {Γ = Γ} z)))
                    [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]v)
             ≡ var f' (∈-++ᶜʳ {Γ = Γ} z)

sub-wk-var-r {Γ} {B} Θ z W f f' =
  trans
    (castᵛ-≡ (castOf {Γ} {B} Θ)
      (sub-≡ᵛ (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) (refl)
        (var-ren-img-≡ (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                       (∈-++ᶜʳ {Γ = Γ} z) f
                       (cong-ren-img-r (wk-ren {A = B}) z) f)))
    (sub-var-r Θ z W f f')

sub-wk-var-l : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ} → (z : A ∈[ ρ ] Γ)
             → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
             → (f f' : ¬ Eternal A → grade-++ᶜˡ ρ Θ ≾ᵣ uᵣ)
             → castᵛ (castOf {Γ} {B} Θ)
                 ((V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                            (var f (∈-++ᶜˡ {Γ = Γ} Θ z)))
                    [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]v)
             ≡ var f' (∈-++ᶜˡ {Γ = Γ} Θ z)

sub-wk-var-l {Γ} {B} Θ z W f f' =
  trans
    (castᵛ-≡ (castOf {Γ} {B} Θ)
      (sub-≡ᵛ (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) (refl)
        (var-ren-img-≡ (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                       (∈-++ᶜˡ {Γ = Γ} Θ z) f
                       (cong-ren-img-l (wk-ren {A = B}) Θ z) f)))
    (sub-var-l Θ z W f f')

sub-wk-var : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ} → (y : A ∈[ ρ ] (Γ ++ᶜ Θ))
           → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
           → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
           → castᵛ (castOf {Γ} {B} Θ)
               ((V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) (var f y))
                  [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]v)
           ≡ var f' y

sub-wk-var {Γ} {B} Θ {A} {ρ} y W f f' with ∈-++ᶜ-split Γ Θ y in eq

... | inj₂ z
  rewrite ∈-++ᶜ-split-inj₂ Γ Θ y z eq = sub-wk-var-r Θ z W f f'

... | inj₁ (ρ' , z) =
  subst (λ t → (fu f'u : ¬ Eternal A → proj₁ t ≾ᵣ uᵣ)
             → castᵛ (castOf {Γ} {B} Θ)
                 ((V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                            (var fu (proj₂ t)))
                    [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]v)
             ≡ var f'u (proj₂ t))
        (sym (∈-++ᶜ-split-inj₁ Γ Θ y z eq))
        (λ fu f'u → sub-wk-var-l Θ z W fu f'u)
        f f'

-- SUBSTITUTING FOR A FRESHLY WEAKENED VARIABLE
--
-- Mutual induction on the term, at an arbitrary suffix: each binding former
-- grows it, which costs nothing — `cong-ren {Θ ∷ A} r` *is*
-- `cong-∷-ren (cong-ren {Θ} r)` and `split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ ∷ A})` *is*
-- `Tl-∷ (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))`, both definitionally, and
-- `split-l` is unchanged so the substituted value keeps its type. What is left
-- per case is pushing the cast through the former and reconciling the two
-- (equal) context proofs by `castᶜ-irr` — whose two arguments must be given
-- explicitly, since nothing determines them.

mutual

  sub-wk-V : ∀ {Γ B} → (Θ : Ctx) → ∀ {A} → (U : (Γ ++ᶜ Θ) ⊢V⦂ A)
           → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
           → castᵛ (castOf {Γ} {B} Θ)
               ((V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) U)
                  [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]v)
           ≡ U

  sub-wk-V {Γ} {B} Θ (var f y) W = sub-wk-var Θ y W f f
  sub-wk-V {Γ} {B} Θ (const c) W = (cast-const (castOf {Γ} {B} Θ))
  sub-wk-V {Γ} {B} Θ ⋆         W = (cast-⋆ (castOf {Γ} {B} Θ))
  sub-wk-V {Γ} {B} Θ ⦉ V₁ , V₂ ⦊ W =
    trans ((cast-pair (castOf {Γ} {B} Θ)))
             (cong₂ ⦉_,_⦊ (sub-wk-V Θ V₁ W) (sub-wk-V Θ V₂ W))
  sub-wk-V {Γ} {B} Θ {A = A ⇒ C} (lam M) W =
    trans ((cast-lam (castOf {Γ} {B} Θ) _))
             (cong lam (trans ((castᶜ-irr (cong (_∷ A) (castOf {Γ} {B} Θ))
                                               (castOf {Γ} {B} (Θ ∷ A)) _))
                              (sub-wk-C (Θ ∷ A) M W)))

  sub-wk-C : ∀ {Γ B} → (Θ : Ctx) → ∀ {C} → (M : (Γ ++ᶜ Θ) ⊢C⦂ C)
           → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
           → castᶜ (castOf {Γ} {B} Θ)
               ((C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) M)
                  [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]c)
           ≡ M

  sub-wk-C {Γ} {B} Θ (return V) W =
    trans ((cast-ret (castOf {Γ} {B} Θ))) (cong return (sub-wk-V Θ V W))

  sub-wk-C {Γ} {B} Θ (_⨟_ {A = A} {ε = ε} M N) W =
    trans ((cast-seq (castOf {Γ} {B} Θ)))
      (cong₂ _⨟_ (sub-wk-C Θ M W)
             (trans ((castᶜ-irr
                                (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (castOf {Γ} {B} Θ))
                                (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))
                       (sub-wk-C (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)))

  sub-wk-C {Γ} {B} Θ (V₁ · V₂) W =
    trans ((cast-app (castOf {Γ} {B} Θ)))
             (cong₂ _·_ (sub-wk-V Θ V₁ W) (sub-wk-V Θ V₂ W))

  sub-wk-C {Γ} {B} Θ (match_`in_ {A = A} {B = B'} V N) W =
    trans ((cast-match (castOf {Γ} {B} Θ)))
      (cong₂ match_`in_ (sub-wk-V Θ V W)
               (trans ((castᶜ-irr
                                  (cong (λ Γ₀ → Γ₀ ∷ A ∷ B') (castOf {Γ} {B} Θ))
                                  (castOf {Γ} {B} (Θ ∷ A ∷ B')) _))
                         (sub-wk-C (Θ ∷ A ∷ B') N W)))

  sub-wk-C {Γ} {B} Θ (absurd V) W =
    trans ((cast-absurd (castOf {Γ} {B} Θ)))
             (cong absurd (sub-wk-V Θ V W))

  sub-wk-C {Γ} {B} Θ (perform op V M) W =
    trans ((cast-perform (castOf {Γ} {B} Θ)))
      (cong₂ (perform _) (sub-wk-V Θ V W)
                 (trans ((castᶜ-irr
                                    (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                                    ∷ type-of-gtype (arity op))
                                          (castOf {Γ} {B} Θ))
                                    (castOf {Γ} {B}
                                      (Θ ⟨ mapᵉ (op-grade op) ⟩
                                         ∷ type-of-gtype (arity op))) _))
                           (sub-wk-C (Θ ⟨ mapᵉ (op-grade op) ⟩
                                        ∷ type-of-gtype (arity op)) M W)))

  sub-wk-C {Γ} {B} Θ (delay τ M) W =
    trans ((cast-delay (castOf {Γ} {B} Θ)))
      (cong (delay _) (trans ((castᶜ-irr
                                  (cong (_⟨ of-natʳ τ ⟩) (castOf {Γ} {B} Θ))
                                  (castOf {Γ} {B} (Θ ⟨ of-natʳ τ ⟩)) _))
                         (sub-wk-C (Θ ⟨ of-natʳ τ ⟩) M W)))

  sub-wk-C {Γ} {B} Θ (box {A = A} {ρ = ρ} V M) W =
    trans ((cast-box (castOf {Γ} {B} Θ)))
      (cong₂ box (trans ((castᵛ-irr (cong (_⟨ ρ ⟩) (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ⟨ ρ ⟩)) _))
                       (sub-wk-V (Θ ⟨ ρ ⟩) V W))
             (trans ((castᶜ-irr (cong (_∷ [ ρ ] A) (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ∷ [ ρ ] A)) _))
                       (sub-wk-C (Θ ∷ [ ρ ] A) M W)))

  sub-wk-C {Γ} {B} Θ (coerce p M) W =
    trans ((cast-coerce (castOf {Γ} {B} Θ)))
             (coerce-≡ (sub-wk-C Θ M W))

  -- `handle`: dispatch on whether the weakened type is eternal. Matching a `Dec`
  -- *argument* rather than `with eternal? B` is what keeps this typeable — a
  -- `with` would abstract `eternal? B` in the goal, and the two halves' own
  -- statements (which re-elaborate it) would then no longer match.
  sub-wk-C {Γ} {B} Θ (handle M `with H `in N) W = go (eternal? B)
    where
      go : Dec (Eternal B) → _
      go (yes et) = sub-wk-handle-et Θ et M H N W
      go (no ¬et) = sub-wk-handle-ne Θ ¬et M H N W

  sub-wk-C {Γ} {B} Θ (unbox {A = A} x rel M) W =
    trans ((cast-unbox (castOf {Γ} {B} Θ)))
      (unbox-≡ (unbox-rvar-wk Θ x W)
        (trans ((castᶜ-irr (cong (_∷ A) (castOf {Γ} {B} Θ))
                                   (castOf {Γ} {B} (Θ ∷ A)) _))
                  (sub-wk-C (Θ ∷ A) M W)))

  -- `sub-wk-C` with its context given by an equation rather than literally, so
  -- that the eternal `handle` clause below can recurse on the bare subterm:
  -- casting the argument into shape is not structurally smaller, and the
  -- termination checker rejects it.

  sub-wk-C-cast : ∀ {Γ B Γ₀} → (Θ : Ctx) → (e : Γ₀ ≡ Γ ++ᶜ Θ) → ∀ {C}
                → (M : Γ₀ ⊢C⦂ C)
                → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
                → castᶜ (castOf {Γ} {B} Θ)
                    ((C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                               (subst (_⊢C⦂ C) e M))
                       [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]c)
                ≡ subst (_⊢C⦂ C) e M

  sub-wk-C-cast Θ refl M W = sub-wk-C Θ M W

  -- `handle`, eternal. `restrict-ren wk-ren` is `wk-ren` there, so the clause is
  -- weakened by the eternal `B` and then substituted at it — another instance of
  -- `sub-wk-C`, at the *splitting's own halves* `split-l z₀ ᴱ` and
  -- `split-r z₀ ᴱ ++ᶜ D`. Taking them rather than `Γ ᴱ`, `Θ ᴱ ++ᶜ D` is what
  -- makes the two ways of naming the substituted variable the *same splitting*,
  -- so `split→∈-unique` settles it outright; the resulting mismatch with the
  -- renaming (which `restrict-wk-clause-≐ʳ` delivers at `Γ ᴱ`, `Θ ᴱ`) is a
  -- relocation of two contexts, which `cong-ren-wk-cast-≐ʳ` discharges by
  -- matching both equalities. The transports left over form a loop.

  sub-wk-handle-et : ∀ {Γ B} → (Θ : Ctx) → ∀ {A B' ε ε'}
                   → (et : Eternal B)
                   → (M : (Γ ++ᶜ Θ) ⊢C⦂ A ‼ ε)
                   → (H : (op : Op) → (ε'' : E) →
                            (Γ ++ᶜ Θ) ᴱ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ]
                                  (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                            ⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                   → (N : (Γ ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε')
                   → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
                   → castᶜ (castOf {Γ} {B} Θ)
                       ((C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                                  (handle M `with H `in N))
                          [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]c)
                   ≡ (handle M `with H `in N)

  sub-wk-handle-et {Γ} {B} Θ {A = A} {B' = B'} {ε = ε} et M H N W
    rewrite eternal?-yes et =
    trans ((cast-handle (castOf {Γ} {B} Θ)))
      (handle-≡ (sub-wk-C Θ M W)
        (λ op ε'' → clause op ε'')
        (trans ((castᶜ-irr
                           (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (castOf {Γ} {B} Θ))
                           (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))
                  (sub-wk-C (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)))
    where
      z₀ = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})

      e₁ : (Γ ++ᶜ Θ) ᴱ ≡ Γ ᴱ ++ᶜ Θ ᴱ
      e₁ = ᴱ-++ᶜ Γ Θ

      e₂ : ((Γ ∷ B) ++ᶜ Θ) ᴱ ≡ (Γ ᴱ ∷ B) ++ᶜ Θ ᴱ
      e₂ = trans (ᴱ-++ᶜ (Γ ∷ B) Θ)
                 (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-keep {Γ} {B} et))

      clause : (op : Op) → (ε'' : E) → _
      clause op ε'' =
        trans (castᶜ-≡ cOut (substᶜ-≡ bigE (sub-≡ᶜ v (refl) ren-step)))
          (trans ((cong (λ t → castᶜ cOut (subst (_⊢C⦂ CT) bigE t))
                                sub-step))
            (trans (reshape)
              (trans (substᶜ-≡ resid (sub-wk-C-cast Θ₀ F₁ (H op ε'') W₁))
                        ((trans (subst-fuseᶜ F₁ resid (H op ε''))
                                     (subst-loopᶜ _ (H op ε'')))))))
        where
          D = [] ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B' ‼ ε'')

          CT = B' ‼ (op-grade op ·ₑ ε'')

          s = split-++ʳ (∈-ᴱ-split et z₀) D

          -- the transport the substitution's own eternal clause applies
          bigE : split-l (split→∈ s) ++ᶜ split-r (split→∈ s)
               ≡ (split-l z₀ ++ᶜ split-r z₀) ᴱ ++ᶜ D
          bigE = trans (cong₂ _++ᶜ_ (split→∈-split-l s) (split→∈-split-r s))
                   (trans (sym (++ᶜ-assoc ((split-l z₀) ᴱ) ((split-r z₀) ᴱ) D))
                          (cong (_++ᶜ D) (sym (ᴱ-++ᶜ (split-l z₀) (split-r z₀)))))

          cOut : (split-l z₀ ++ᶜ split-r z₀) ᴱ ++ᶜ D ≡ (Γ ++ᶜ Θ) ᴱ ++ᶜ D
          cOut = cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D) (castOf {Γ} {B} Θ)

          -- the renaming, fused: at this suffix the associativity legs are `refl`
          rfuse : cong-ren {Γ'' = D} (restrict-ren {Ξ = []}
                                       (cong-ren {Γ'' = Θ} (wk-ren {A = B})))
                ≐ʳ (eq-ren (cong (_++ᶜ D) e₁)
                    ∘ʳ cong-ren {Γ'' = Θ ᴱ ++ᶜ D} (wk-ren {A = B})
                    ∘ʳ eq-ren (cong (_++ᶜ D) (sym e₂)))
          rfuse =
            ≐ʳ-trans (restrict-wk-clause-≐ʳ et Θ D e₁ e₂)
                     (∘ʳ-≐ʳ ≐ʳ-refl
                           (∘ʳ-≐ʳ (≐ʳ-trans (∘ʳ-identityˡ-≐ʳ _)
                                           (∘ʳ-identityʳ-≐ʳ _))
                                 ≐ʳ-refl))

          -- the recursion's context: the splitting's own halves
          Γ₀ = split-l z₀ ᴱ
          Θ₀ = split-r z₀ ᴱ ++ᶜ D

          eLΓ : split-l z₀ ᴱ ≡ Γ ᴱ
          eLΓ = cong _ᴱ (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B} {Θ}))

          eRΘ : split-r z₀ ᴱ ++ᶜ D ≡ Θ ᴱ ++ᶜ D
          eRΘ = cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D)
                     (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B} {Θ}))

          eIn : Γ ᴱ ++ᶜ (Θ ᴱ ++ᶜ D) ≡ Γ₀ ++ᶜ Θ₀
          eIn = sym (cong₂ _++ᶜ_ eLΓ eRΘ)

          eOut′ : (Γ₀ ∷ B) ++ᶜ Θ₀ ≡ (Γ ᴱ ∷ B) ++ᶜ (Θ ᴱ ++ᶜ D)
          eOut′ = cong₂ (λ Γ₁ Θ₁ → (Γ₁ ∷ B) ++ᶜ Θ₁) eLΓ eRΘ

          F₁ : (Γ ++ᶜ Θ) ᴱ ++ᶜ D ≡ Γ₀ ++ᶜ Θ₀
          F₁ = trans (cong (_++ᶜ D) e₁) eIn

          F₂ : (Γ₀ ∷ B) ++ᶜ Θ₀ ≡ ((Γ ∷ B) ++ᶜ Θ) ᴱ ++ᶜ D
          F₂ = trans eOut′ (cong (_++ᶜ D) (sym e₂))

          wk₀ = cong-ren {Γ'' = Θ₀} (wk-ren {A = B})

          -- the two names for the substituted variable are the same splitting
          x₁ = split→∈ (split-≡-++ᶜ {Γ₀ ∷ B} {Θ₀})
          v  = split→∈ s

          var-eq : subst (λ Γ₁ → B ∈[ ctx-grade Θ₀ ] Γ₁) F₂ x₁ ≡ v
          var-eq = split→∈-unique F₂ (split-≡-++ᶜ {Γ₀ ∷ B} {Θ₀}) s

          Wᴱ : split-l v ⊢V⦂ B
          Wᴱ = subst (_⊢V⦂ B) (sym (split→∈-split-l s))
                     (eternal-val-restrict et W)

          eW : split-l x₁ ≡ split-l v
          eW = trans (split-l-cast F₂ x₁) (cong split-l var-eq)

          W₁ : split-l x₁ ⊢V⦂ B
          W₁ = subst (_⊢V⦂ B) (sym eW) Wᴱ

          Y = C-rename wk₀ (subst (_⊢C⦂ CT) F₁ (H op ε''))

          rfuse2 : cong-ren {Γ'' = D} (restrict-ren {Ξ = []}
                              (cong-ren {Γ'' = Θ} (wk-ren {A = B})))
                 ≐ʳ (eq-ren (cong (_++ᶜ D) e₁)
                     ∘ʳ (eq-ren eIn ∘ʳ wk₀ ∘ʳ eq-ren eOut′)
                     ∘ʳ eq-ren (cong (_++ᶜ D) (sym e₂)))
          rfuse2 =
            ≐ʳ-trans rfuse
              (∘ʳ-≐ʳ ≐ʳ-refl
                (∘ʳ-≐ʳ (cong-ren-wk-cast-≐ʳ Γ₀ (Γ ᴱ) Θ₀ (Θ ᴱ ++ᶜ D)
                                          eLΓ eRΘ eIn eOut′)
                      ≐ʳ-refl))

          -- the renaming, split into its legs, each `eq-ren` becoming its
          -- transport
          ren-step : C-rename (cong-ren {Γ'' = D} (restrict-ren {Ξ = []}
                                  (cong-ren {Γ'' = Θ} (wk-ren {A = B}))))
                              (H op ε'')
                   ≡ subst (_⊢C⦂ CT) F₂ Y
          ren-step =
            trans (C-rename-≡ rfuse2 (H op ε''))
              (trans (C-rename-∘ _ _ (H op ε''))
                (trans (C-rename-cong _
                            (C-rename-eq-≡ (cong (_++ᶜ D) e₁) ≐ʳ-refl _))
                  (trans (C-rename-∘ _ (eq-ren (cong (_++ᶜ D) (sym e₂))) _)
                    (trans
                      (C-rename-cong _
                        (trans (C-rename-∘ (eq-ren eIn) _ _)
                          (trans (C-rename-cong _
                                      (C-rename-eq-≡ eIn ≐ʳ-refl _))
                            (trans (C-rename-∘ wk₀ (eq-ren eOut′) _)
                                      (C-rename-eq-≡ eOut′ ≐ʳ-refl _)))))
                      (trans
                        (C-rename-eq-≡ (cong (_++ᶜ D) (sym e₂)) ≐ʳ-refl _)
                        ((trans (subst-fuseᶜ eOut′ (cong (_++ᶜ D) (sym e₂)) _)
                                     (cong (λ t → subst (_⊢C⦂ CT) F₂ (C-rename wk₀ t))
                                           (subst-fuseᶜ (cong (_++ᶜ D) e₁) eIn
                                                        (H op ε''))))))))))

          -- the substitution, moved across the outer transport
          sub-step : (subst (_⊢C⦂ CT) F₂ Y) [ v ↦ Wᴱ ]c
                   ≡ subst (_⊢C⦂ CT)
                       (cong₂ _++ᶜ_ eW
                              (trans (split-r-cast F₂ x₁) (cong split-r var-eq)))
                       (Y [ x₁ ↦ W₁ ]c)
          sub-step =
            sub-cast-C′ F₂ Y x₁ v var-eq W₁ Wᴱ (subst-subst-sym′ eW Wᴱ)

          resid : Γ₀ ++ᶜ Θ₀ ≡ (Γ ++ᶜ Θ) ᴱ ++ᶜ D
          resid = sym F₁

          Z = Y [ x₁ ↦ W₁ ]c

          G : split-l x₁ ++ᶜ split-r x₁ ≡ split-l v ++ᶜ split-r v
          G = cong₂ _++ᶜ_ eW (trans (split-r-cast F₂ x₁) (cong split-r var-eq))

          -- the goal's three transports and the recursion's own one both take
          -- `Z` to the clause's context, so they agree by `uip`
          reshape : castᶜ cOut (subst (_⊢C⦂ CT) bigE (subst (_⊢C⦂ CT) G Z))
                  ≡ subst (_⊢C⦂ CT) resid (castᶜ (castOf {Γ₀} {B} Θ₀) Z)
          reshape =
            trans (castᶜ≡subst cOut _)
              (trans (cong (subst (_⊢C⦂ CT) cOut) (subst-fuseᶜ G bigE Z))
                (trans (subst-fuseᶜ (trans G bigE) cOut Z)
                  (sym (trans (cong (subst (_⊢C⦂ CT) resid)
                                    (castᶜ≡subst (castOf {Γ₀} {B} Θ₀) Z))
                         (trans (subst-fuseᶜ (castOf {Γ₀} {B} Θ₀) resid Z)
                                (cong (λ z → subst (_⊢C⦂ CT) z Z)
                                      (uip {p = trans (castOf {Γ₀} {B} Θ₀) resid}
                                           {q = trans (trans G bigE) cOut})))))))

  -- `handle`, non-eternal. The clause's renaming `restrict-ren (cong-ren {Θ}
  -- wk-ren)` is identity-like (`restrict-wk-≐ʳ`), so the clause is transported
  -- three times — by it, by the substitution's `ᴱ-drop-split`, and by the outer
  -- cast — around a loop, which `subst-loop₃` collapses.
  --
  -- Stated over the unreduced substitution and doing its own `with`, so that the
  -- `yes` case is dismissed by absurdity rather than appearing in any statement.

  sub-wk-handle-ne : ∀ {Γ B} → (Θ : Ctx) → ∀ {A B' ε ε'}
                   → ¬ Eternal B
                   → (M : (Γ ++ᶜ Θ) ⊢C⦂ A ‼ ε)
                   → (H : (op : Op) → (ε'' : E) →
                            (Γ ++ᶜ Θ) ᴱ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ]
                                  (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                            ⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                   → (N : (Γ ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε')
                   → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
                   → castᶜ (castOf {Γ} {B} Θ)
                       ((C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                                  (handle M `with H `in N))
                          [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]c)
                   ≡ (handle M `with H `in N)

  sub-wk-handle-ne {Γ} {B} Θ {A = A} {B' = B'} {ε = ε} ¬et M H N W
    rewrite eternal?-no ¬et =
    trans ((cast-handle (castOf {Γ} {B} Θ)))
      (handle-≡ (sub-wk-C Θ M W)
        (λ op ε'' → clause op ε'')
        (trans ((castᶜ-irr
                           (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (castOf {Γ} {B} Θ))
                           (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))
                  (sub-wk-C (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)))
    where
      z₀ = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})

      e₁ : (Γ ++ᶜ Θ) ᴱ ≡ ((Γ ∷ B) ++ᶜ Θ) ᴱ
      e₁ = sym (trans (ᴱ-drop-split ¬et z₀) (cong _ᴱ (castOf {Γ} {B} Θ)))

      clause : (op : Op) → (ε'' : E) → _
      clause op ε'' =
        trans
          (castᶜ-≡ (cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D) (castOf {Γ} {B} Θ))
            (substᶜ-≡′ (λ Γ₀ → Γ₀ ++ᶜ D)
                       {C = CT} (ᴱ-drop-split ¬et z₀)
              (C-rename-eq-≡ (cong (_++ᶜ D) e₁)
                (≐ʳ-trans (cong-ren-≐ʳ D (restrict-wk-≐ʳ ¬et Θ e₁))
                          (cong-ren-eq-ren-≐ʳ D e₁))
                (H op ε''))))
          (collapse)
        where
          D = [] ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B' ‼ ε'')

          CT = B' ‼ (op-grade op ·ₑ ε'')

          collapse : castᶜ (cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D) (castOf {Γ} {B} Θ))
                       (subst (λ Γ₀ → (Γ₀ ++ᶜ D) ⊢C⦂ CT) (ᴱ-drop-split ¬et z₀)
                         (subst (_⊢C⦂ CT) (cong (_++ᶜ D) e₁) (H op ε'')))
                   ≡ H op ε''
          collapse =
            trans (castᶜ≡subst (cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D) (castOf {Γ} {B} Θ)) _)
              (trans (cong (subst (_⊢C⦂ CT)
                              (cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D) (castOf {Γ} {B} Θ)))
                           (subst-++ᶜʳ D (ᴱ-drop-split ¬et z₀) _))
                     (subst-loop₃ (cong (_++ᶜ D) e₁)
                                  (cong (_++ᶜ D) (ᴱ-drop-split ¬et z₀))
                                  (cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D) (castOf {Γ} {B} Θ))
                                  (H op ε'')))

