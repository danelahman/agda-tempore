------------------------------------------------------------------
-- The context modality on renamings, and its left adjoints     --
--                                                              --
-- A context morphism `Γ → Δ` is a renaming `Ren Q Δ Γ`,        --
-- sending each variable of `Δ` to one of `Γ`. Contexts and     --
-- these morphisms up to `_≐ʳ_`, equality of positions, form a  --
-- category, on which `L_ρ = _⟨ ρ ⟩` acts by `⟨⟩ʳ`. Each        --
-- program context `P` gives a component, with the terminal     --
-- object `⌜ P ⌝ᵖ`.                                             --
--                                                              --
-- Left adjoint. A representation of `Hom(Γ, L_ρ -)` is a       --
-- context `E` and a bijection `Hom(E, Δ) ≅ Hom(Γ, L_ρ Δ)`      --
-- natural in `Δ` (`HomIso`); the representations determine an  --
-- adjunction (`adjunction`).                                   --
--                                                              --
-- Parametric right adjoint. `L_ρ` is one when the functor it   --
-- induces into the slice over `L_ρ ⌜ P ⌝ᵖ` has a left          --
-- adjoint (M. Weber, Familial 2-functors and parametric        --
-- right adjoints, Theory Appl. Categ. 18 (2007), Def. 2.3,     --
-- which credits R. Street, The petit topos of globular sets,   --
-- J. Pure Appl. Algebra 154 (2000)): for each                  --
-- `s : Γ → L_ρ ⌜ P ⌝ᵖ`, a representation of the maps           --
-- `Γ → L_ρ Δ` over `s`. Every context has exactly one such     --
-- `s` (`section`, `section-unique`), so every map lies over    --
-- it, and `PRA` asks for a representation of                   --
-- `Hom(Γ, L_ρ -)` at each `s`. So `L_ρ` is a parametric        --
-- right adjoint iff it has a left adjoint                      --
-- (`PRA⇔LeftAdjoint`).                                         --
--                                                              --
-- At the empty scope the left adjoints are built from          --
-- residuals: `e` is the residual of `g` by `ρ` when            --
-- `e ≾ d ⇔ g ≾ d · ρ` for all `d` (`IsResidual`), the least    --
-- `d` with `g ≾ d · ρ`. A lowering of `Γ` by `ρ` is a context  --
-- of the variables of `Γ` at grades `≾ ⊤ · ρ`, each at the     --
-- residual of its grade (`Lowering`).                          --
--                                                              --
-- Results:                                                     --
--   `left-adjoint-at-𝟏`: at `ρ` entailed equal to `𝟏`, `L_ρ`   --
--      has the left adjoint `E Γ = Γ`;                         --
--   `left-adjoint⇔lowering`, `PRA⇔lowering`: at the empty      --
--      scope, under no hypotheses and at a constant `ρ`, `L_ρ` --
--      has a left adjoint iff every context has a lowering by  --
--      `ρ`;                                                    --
--   `left-adjoint⇒residual`, `PRA⇒residual`: a left adjoint    --
--      gives the residual by `ρ` of every `g ≾ ⊤ · ρ`, and     --
--      only those have one (`residual-bounded`).               --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Typing.Renaming.ContextModality (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import PolymorphicCalculus.Syntax.Grades         S
open import PolymorphicCalculus.Syntax.Types          S
open import PolymorphicCalculus.Syntax.Contexts       S
open import PolymorphicCalculus.Hypotheses            S using (Hyps; ∅ᴴ; _⊩_≾̂ᵣ_)
open import PolymorphicCalculus.Hypotheses.Instances  S using (val-≾ᵣ; val-≾ᵣ⁻)
open import PolymorphicCalculus.Typing.Renaming       S
  using (Ren; pos; ty; gr; dfs; id-ren; _∘ʳ_; ⟨⟩ʳ; ⟨⟩-remove; ⟨⟩-insert)

------------------------------------------------------------------------
-- Equality of renamings, and the category laws

infix 4 _≐ʳ_

record _≐ʳ_ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} (r r' : Ren Q Γ Γ') : Set where
  constructor mk≐ʳ
  field
    at : ∀ i → pos r i ≡ pos r' i

open _≐ʳ_ public

module _ {Θ : Scope} {Q : Hyps Θ} where

  ≐ʳ-refl : ∀ {n m} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {r : Ren Q Γ Γ'} → r ≐ʳ r
  ≐ʳ-refl = mk≐ʳ λ i → refl

  ≐ʳ-sym : ∀ {n m} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {r r' : Ren Q Γ Γ'} → r ≐ʳ r' → r' ≐ʳ r
  ≐ʳ-sym e = mk≐ʳ λ i → sym (at e i)

  ≐ʳ-trans : ∀ {n m} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {r r' r'' : Ren Q Γ Γ'}
           → r ≐ʳ r' → r' ≐ʳ r'' → r ≐ʳ r''
  ≐ʳ-trans e e' = mk≐ʳ λ i → trans (at e i) (at e' i)

  ∘ʳ-≐ʳ : ∀ {n m k} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {Γ'' : OCtx Θ k}
            {s s' : Ren Q Γ' Γ''} {r r' : Ren Q Γ Γ'}
        → s ≐ʳ s' → r ≐ʳ r' → (s ∘ʳ r) ≐ʳ (s' ∘ʳ r')
  ∘ʳ-≐ʳ {s = s} {r' = r'} e e' = mk≐ʳ λ i → trans (cong (pos s) (at e' i)) (at e (pos r' i))

  ∘ʳ-assoc-≐ʳ : ∀ {n m k l} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {Γ'' : OCtx Θ k}
                  {Γ''' : OCtx Θ l}
              → (t : Ren Q Γ'' Γ''') → (s : Ren Q Γ' Γ'') → (r : Ren Q Γ Γ')
              → ((t ∘ʳ s) ∘ʳ r) ≐ʳ (t ∘ʳ (s ∘ʳ r))
  ∘ʳ-assoc-≐ʳ t s r = mk≐ʳ λ i → refl

  ∘ʳ-identityˡ-≐ʳ : ∀ {n m} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} → (r : Ren Q Γ Γ')
                  → (id-ren ∘ʳ r) ≐ʳ r
  ∘ʳ-identityˡ-≐ʳ r = mk≐ʳ λ i → refl

  ∘ʳ-identityʳ-≐ʳ : ∀ {n m} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} → (r : Ren Q Γ Γ')
                  → (r ∘ʳ id-ren) ≐ʳ r
  ∘ʳ-identityʳ-≐ʳ r = mk≐ʳ λ i → refl

  -- `L_ρ` is a functor

  ⟨⟩ʳ-≐ʳ : ∀ {n m} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {ρ : RExp Θ} {r r' : Ren Q Γ Γ'}
         → r ≐ʳ r' → ⟨⟩ʳ ρ r ≐ʳ ⟨⟩ʳ ρ r'
  ⟨⟩ʳ-≐ʳ e = mk≐ʳ (at e)

  ⟨⟩ʳ-id-≐ʳ : ∀ {n} {Γ : OCtx Θ n} {ρ : RExp Θ} → ⟨⟩ʳ ρ (id-ren {Q = Q} {Γ = Γ}) ≐ʳ id-ren
  ⟨⟩ʳ-id-≐ʳ = mk≐ʳ λ i → refl

  ⟨⟩ʳ-∘-≐ʳ : ∀ {n m k} {Γ : OCtx Θ n} {Γ' : OCtx Θ m} {Γ'' : OCtx Θ k} {ρ : RExp Θ}
           → (s : Ren Q Γ' Γ'') → (r : Ren Q Γ Γ')
           → ⟨⟩ʳ ρ (s ∘ʳ r) ≐ʳ (⟨⟩ʳ ρ s ∘ʳ ⟨⟩ʳ ρ r)
  ⟨⟩ʳ-∘-≐ʳ s r = mk≐ʳ λ i → refl

------------------------------------------------------------------------
-- Representations, left adjoints and parametric right adjoints

module _ {Θ : Scope} (Q : Hyps Θ) where

  -- a bijection `Hom(E, Δ) ≅ Hom(Γ, Δ ⟨ ρ ⟩)`, natural in `Δ`

  record HomIso (ρ : RExp Θ) {n k : ℕ} (Γ : OCtx Θ n) (E : OCtx Θ k) : Set where
    field
      φ      : ∀ {m} {Δ : OCtx Θ m} → Ren Q Δ E → Ren Q (Δ ⟨ ρ ⟩) Γ
      ψ      : ∀ {m} {Δ : OCtx Θ m} → Ren Q (Δ ⟨ ρ ⟩) Γ → Ren Q Δ E
      φ-cong : ∀ {m} {Δ : OCtx Θ m} {g g' : Ren Q Δ E} → g ≐ʳ g' → φ g ≐ʳ φ g'
      ψ-cong : ∀ {m} {Δ : OCtx Θ m} {f f' : Ren Q (Δ ⟨ ρ ⟩) Γ} → f ≐ʳ f' → ψ f ≐ʳ ψ f'
      ψ∘φ    : ∀ {m} {Δ : OCtx Θ m} → (g : Ren Q Δ E) → ψ (φ g) ≐ʳ g
      φ∘ψ    : ∀ {m} {Δ : OCtx Θ m} → (f : Ren Q (Δ ⟨ ρ ⟩) Γ) → φ (ψ f) ≐ʳ f
      φ-nat  : ∀ {m m'} {Δ : OCtx Θ m} {Δ' : OCtx Θ m'} → (h : Ren Q Δ' Δ) → (g : Ren Q Δ E)
             → φ (g ∘ʳ h) ≐ʳ (φ g ∘ʳ ⟨⟩ʳ ρ h)

  LeftAdjoint : RExp Θ → Set
  LeftAdjoint ρ = ∀ {n} → (Γ : OCtx Θ n) → Σ[ k ∈ ℕ ] Σ[ E ∈ OCtx Θ k ] HomIso ρ Γ E

  -- an adjunction `E ⊣ L_ρ`: `E` on contexts and on morphisms, functorial,
  -- with bijections natural in `Δ` (`hom-iso`) and in `Γ` (`φ-natᴳ`)

  record Adjunction (ρ : RExp Θ) : Set where
    field
      E-len    : ∀ {n} → OCtx Θ n → ℕ
      E-ctx    : ∀ {n} → (Γ : OCtx Θ n) → OCtx Θ (E-len Γ)
      hom-iso  : ∀ {n} → (Γ : OCtx Θ n) → HomIso ρ Γ (E-ctx Γ)
      E-ren    : ∀ {n n'} {Γ : OCtx Θ n} {Γ' : OCtx Θ n'}
               → Ren Q Γ' Γ → Ren Q (E-ctx Γ') (E-ctx Γ)
      E-ren-id : ∀ {n} {Γ : OCtx Θ n} → E-ren (id-ren {Γ = Γ}) ≐ʳ id-ren
      E-ren-∘  : ∀ {n n' n''} {Γ : OCtx Θ n} {Γ' : OCtx Θ n'} {Γ'' : OCtx Θ n''}
               → (r₁ : Ren Q Γ' Γ) → (r₂ : Ren Q Γ'' Γ')
               → E-ren (r₁ ∘ʳ r₂) ≐ʳ (E-ren r₁ ∘ʳ E-ren r₂)
      φ-natᴳ   : ∀ {n n' m} {Γ : OCtx Θ n} {Γ' : OCtx Θ n'} {Δ : OCtx Θ m}
               → (r : Ren Q Γ' Γ) → (g : Ren Q Δ (E-ctx Γ'))
               → HomIso.φ (hom-iso Γ) (E-ren r ∘ʳ g) ≐ʳ (r ∘ʳ HomIso.φ (hom-iso Γ') g)

  -- the representations determine the adjunction, with
  -- `E-ren r = ψ_Γ (r ∘ φ_Γ' id)`

  adjunction : ∀ {ρ} → LeftAdjoint ρ → Adjunction ρ
  adjunction {ρ} la = record
    { E-len    = λ Γ → proj₁ (la Γ)
    ; E-ctx    = E-ctx
    ; hom-iso  = H
    ; E-ren    = E-ren
    ; E-ren-id = E-ren-id
    ; E-ren-∘  = E-ren-∘
    ; φ-natᴳ   = φ-natᴳ
    }
    where
    E-ctx : ∀ {n} → (Γ : OCtx Θ n) → OCtx Θ (proj₁ (la Γ))
    E-ctx Γ = proj₁ (proj₂ (la Γ))

    H : ∀ {n} → (Γ : OCtx Θ n) → HomIso ρ Γ (E-ctx Γ)
    H Γ = proj₂ (proj₂ (la Γ))

    module H {n} (Γ : OCtx Θ n) = HomIso (H Γ)

    E-ren : ∀ {n n'} {Γ : OCtx Θ n} {Γ' : OCtx Θ n'} → Ren Q Γ' Γ → Ren Q (E-ctx Γ') (E-ctx Γ)
    E-ren {Γ = Γ} {Γ'} r = H.ψ Γ (r ∘ʳ H.φ Γ' id-ren)

    φ-E-ren : ∀ {n n'} {Γ : OCtx Θ n} {Γ' : OCtx Θ n'} → (r : Ren Q Γ' Γ)
            → H.φ Γ (E-ren r) ≐ʳ (r ∘ʳ H.φ Γ' id-ren)
    φ-E-ren {Γ = Γ} {Γ'} r = H.φ∘ψ Γ (r ∘ʳ H.φ Γ' id-ren)

    φ-inj : ∀ {n m} {Γ : OCtx Θ n} {Δ : OCtx Θ m} {g g' : Ren Q Δ (E-ctx Γ)}
          → H.φ Γ g ≐ʳ H.φ Γ g' → g ≐ʳ g'
    φ-inj {Γ = Γ} {g = g} {g'} e =
      ≐ʳ-trans (≐ʳ-sym (H.ψ∘φ Γ g)) (≐ʳ-trans (H.ψ-cong Γ e) (H.ψ∘φ Γ g'))

    φ-natᴳ : ∀ {n n' m} {Γ : OCtx Θ n} {Γ' : OCtx Θ n'} {Δ : OCtx Θ m}
           → (r : Ren Q Γ' Γ) → (g : Ren Q Δ (E-ctx Γ'))
           → H.φ Γ (E-ren r ∘ʳ g) ≐ʳ (r ∘ʳ H.φ Γ' g)
    φ-natᴳ {Γ = Γ} {Γ'} r g = mk≐ʳ λ i →
      trans (at (H.φ-nat Γ g (E-ren r)) i)
        (trans (at (φ-E-ren r) (pos g i))
          (cong (pos r)
            (trans (sym (at (H.φ-nat Γ' g id-ren) i))
                   (at (H.φ-cong Γ' (∘ʳ-identityˡ-≐ʳ g)) i))))

    E-ren-id : ∀ {n} {Γ : OCtx Θ n} → E-ren (id-ren {Γ = Γ}) ≐ʳ id-ren
    E-ren-id {Γ = Γ} =
      ≐ʳ-trans (H.ψ-cong Γ (∘ʳ-identityˡ-≐ʳ (H.φ Γ id-ren))) (H.ψ∘φ Γ id-ren)

    E-ren-∘ : ∀ {n n' n''} {Γ : OCtx Θ n} {Γ' : OCtx Θ n'} {Γ'' : OCtx Θ n''}
            → (r₁ : Ren Q Γ' Γ) → (r₂ : Ren Q Γ'' Γ')
            → E-ren (r₁ ∘ʳ r₂) ≐ʳ (E-ren r₁ ∘ʳ E-ren r₂)
    E-ren-∘ {Γ'' = Γ''} r₁ r₂ =
      φ-inj (mk≐ʳ λ i →
        trans (at (φ-E-ren (r₁ ∘ʳ r₂)) i)
          (sym (trans (at (φ-natᴳ r₁ (E-ren r₂)) i) (cong (pos r₁) (at (φ-E-ren r₂) i)))))

  -- `Γ` has exactly one morphism into `L_ρ ⌜ defs Γ ⌝ᵖ`

  section : (ρ : RExp Θ) → ∀ {n} → (Γ : OCtx Θ n) → Ren Q (⌜ defs Γ ⌝ᵖ ⟨ ρ ⟩) Γ
  pos (section ρ Γ) ()
  ty  (section ρ Γ) ()
  gr  (section ρ Γ) ()
  dfs (section ρ Γ) = sym (defs-⌜⌝ (defs Γ))

  section-unique : ∀ {ρ n P} {Γ : OCtx Θ n} → (s s' : Ren Q (⌜ P ⌝ᵖ ⟨ ρ ⟩) Γ) → s ≐ʳ s'
  section-unique {P = ∅ᵖ}     s s' = mk≐ʳ λ ()
  section-unique {P = _ ∷ᵖ _} s s' = mk≐ʳ λ ()

  -- for each `s : Γ → L_ρ ⌜ defs Γ ⌝ᵖ`, a representation

  PRA : RExp Θ → Set
  PRA ρ = ∀ {n} → (Γ : OCtx Θ n) → Ren Q (⌜ defs Γ ⌝ᵖ ⟨ ρ ⟩) Γ
        → Σ[ k ∈ ℕ ] Σ[ E ∈ OCtx Θ k ] HomIso ρ Γ E

  LeftAdjoint⇒PRA : ∀ {ρ} → LeftAdjoint ρ → PRA ρ
  LeftAdjoint⇒PRA la Γ _ = la Γ

  PRA⇒LeftAdjoint : ∀ {ρ} → PRA ρ → LeftAdjoint ρ
  PRA⇒LeftAdjoint {ρ} pra Γ = pra Γ (section ρ Γ)

  PRA⇔LeftAdjoint : ∀ {ρ} → (PRA ρ → LeftAdjoint ρ) × (LeftAdjoint ρ → PRA ρ)
  PRA⇔LeftAdjoint = PRA⇒LeftAdjoint , LeftAdjoint⇒PRA

  -- at a grade entailed equal to `𝟏`, the identity is a left adjoint

  left-adjoint-at-𝟏 : ∀ {ρ} → Q ⊩ ρ ≾̂ᵣ 𝟏̂ᵣ → Q ⊩ 𝟏̂ᵣ ≾̂ᵣ ρ → LeftAdjoint ρ
  left-adjoint-at-𝟏 p q {n} Γ = n , Γ , record
    { φ      = λ g → g ∘ʳ ⟨⟩-remove q
    ; ψ      = λ f → f ∘ʳ ⟨⟩-insert p
    ; φ-cong = λ e → mk≐ʳ (at e)
    ; ψ-cong = λ e → mk≐ʳ (at e)
    ; ψ∘φ    = λ _ → mk≐ʳ λ _ → refl
    ; φ∘ψ    = λ _ → mk≐ʳ λ _ → refl
    ; φ-nat  = λ _ _ → mk≐ʳ λ _ → refl
    }

------------------------------------------------------------------------
-- Residuals and lowerings, at the empty scope

-- `e` is the residual of `g` by `ρ`, the least `d` with `g ≾ d · ρ`

record IsResidual (ρ g e : R) : Set where
  field
    res⇒ : ∀ d → e ≾ᵣ d → g ≾ᵣ d ·ᵣ ρ
    ⇒res : ∀ d → g ≾ᵣ d ·ᵣ ρ → e ≾ᵣ d

open IsResidual public

Residual : R → R → Set
Residual ρ g = Σ[ e ∈ R ] IsResidual ρ g e

-- a grade with a residual by `ρ` lies below `⊤ · ρ`

residual-bounded : ∀ {ρ g} → Residual ρ g → g ≾ᵣ ⊤ᵣ ·ᵣ ρ
residual-bounded (e , r) = res⇒ r ⊤ᵣ (≾-⊤ᵣ e)

-- a context of the variables of `Γ` at grades `g ≾ ⊤ · ρ`, each at the
-- residual of its grade by `ρ`

record Lowering (ρ : R) {n : ℕ} (Γ : OCtx ∅ˢ n) : Set where
  field
    size     : ℕ
    ctx      : OCtx ∅ˢ size
    emb      : Fin size → Fin n
    back     : (j : Fin n) → valʳ (lookup-gr Γ j) ≾ᵣ ⊤ᵣ ·ᵣ ρ → Fin size
    emb-back : ∀ j p → emb (back j p) ≡ j
    back-emb : ∀ i p → back (emb i) p ≡ i
    ctx-ty   : ∀ i → lookup-ty ctx i ≡ lookup-ty Γ (emb i)
    ctx-dfs  : defs ctx ≡ defs Γ
    ctx-res  : ∀ i → IsResidual ρ (valʳ (lookup-gr Γ (emb i))) (valʳ (lookup-gr ctx i))

-- lowerings give a left adjoint

lowering⇒left-adjoint : ∀ {ρ} → (∀ {n} → (Γ : OCtx ∅ˢ n) → Lowering ρ Γ)
                      → LeftAdjoint {∅ˢ} ∅ᴴ (rconst ρ)
lowering⇒left-adjoint {ρ} low Γ = size , ctx , record
  { φ      = φ
  ; ψ      = ψ
  ; φ-cong = λ e → mk≐ʳ λ i → cong emb (at e i)
  ; ψ-cong = λ e → mk≐ʳ λ i → back-cong (at e i)
  ; ψ∘φ    = λ g → mk≐ʳ λ i → back-emb (pos g i) _
  ; φ∘ψ    = λ f → mk≐ʳ λ i → emb-back (pos f i) _
  ; φ-nat  = λ _ _ → mk≐ʳ λ _ → refl
  }
  where
  open Lowering (low Γ)

  kept : ∀ {m} {Δ : OCtx ∅ˢ m} → (f : Ren ∅ᴴ (Δ ⟨ rconst ρ ⟩) Γ) → (i : Fin m)
       → valʳ (lookup-gr Γ (pos f i)) ≾ᵣ ⊤ᵣ ·ᵣ ρ
  kept {Δ = Δ} f i = ≾ᵣ-trans (val-≾ᵣ (gr f i)) (·ᵣ-monoˡ-≾ᵣ (≾-⊤ᵣ (valʳ (lookup-gr Δ i))))

  back-cong : ∀ {j j' p p'} → j ≡ j' → back j p ≡ back j' p'
  back-cong {j} {p = p} {p'} refl = cong (back j) (≾ᵣ-irrelevant p p')

  φ : ∀ {m} {Δ : OCtx ∅ˢ m} → Ren ∅ᴴ Δ ctx → Ren ∅ᴴ (Δ ⟨ rconst ρ ⟩) Γ
  pos (φ g) i = emb (pos g i)
  ty  (φ g) i = trans (sym (ctx-ty (pos g i))) (ty g i)
  gr  (φ {Δ = Δ} g) i =
    val-≾ᵣ⁻ (res⇒ (ctx-res (pos g i)) (valʳ (lookup-gr Δ i)) (val-≾ᵣ (gr g i)))
  dfs (φ g) = trans (sym ctx-dfs) (dfs g)

  ψ : ∀ {m} {Δ : OCtx ∅ˢ m} → Ren ∅ᴴ (Δ ⟨ rconst ρ ⟩) Γ → Ren ∅ᴴ Δ ctx
  pos (ψ f) i = back (pos f i) (kept f i)
  ty  (ψ f) i =
    trans (ctx-ty _) (trans (cong (lookup-ty Γ) (emb-back (pos f i) (kept f i))) (ty f i))
  gr  (ψ {Δ = Δ} f) i =
    val-≾ᵣ⁻ (⇒res (ctx-res (back (pos f i) (kept f i))) (valʳ (lookup-gr Δ i))
              (subst (λ j → valʳ (lookup-gr Γ j) ≾ᵣ valʳ (lookup-gr Δ i) ·ᵣ ρ)
                     (sym (emb-back (pos f i) (kept f i))) (val-≾ᵣ (gr f i))))
  dfs (ψ f) = trans ctx-dfs (dfs f)

-- a representation is a lowering, embedded by `φ id`; it is tested
-- against the one-variable contexts `(⌜ defs Γ ⌝ᵖ ∷ A) ⟨ d ⟩`

left-adjoint⇒lowering : ∀ {ρ} → LeftAdjoint {∅ˢ} ∅ᴴ (rconst ρ)
                      → ∀ {n} → (Γ : OCtx ∅ˢ n) → Lowering ρ Γ
left-adjoint⇒lowering {ρ} la Γ = record
  { size     = proj₁ (la Γ)
  ; ctx      = E₀
  ; emb      = emb
  ; back     = λ j p → pos (ψ (into ⊤ᵣ j p)) zero
  ; emb-back = λ j p → ψ-emb (into ⊤ᵣ j p) zero
  ; back-emb = λ i p → ψ-into ⊤ᵣ i p
  ; ctx-ty   = ctx-ty
  ; ctx-dfs  = ctx-dfs
  ; ctx-res  = λ i → record { res⇒ = res⇒′ i ; ⇒res = ⇒res′ i }
  }
  where
  E₀ = proj₁ (proj₂ (la Γ))
  open HomIso (proj₂ (proj₂ (la Γ)))

  emb : Fin (proj₁ (la Γ)) → Fin _
  emb = pos (φ id-ren)

  ctx-ty : ∀ i → lookup-ty E₀ i ≡ lookup-ty Γ (emb i)
  ctx-ty i = sym (ty (φ id-ren) i)

  ctx-dfs : defs E₀ ≡ defs Γ
  ctx-dfs = sym (dfs (φ id-ren))

  D : R → OVType ∅ˢ → OCtx ∅ˢ 1
  D d A = (⌜ defs Γ ⌝ᵖ ∷ A) ⟨ rconst d ⟩

  into : ∀ d j → valʳ (lookup-gr Γ j) ≾ᵣ d ·ᵣ ρ → Ren ∅ᴴ (D d (lookup-ty Γ j) ⟨ rconst ρ ⟩) Γ
  pos (into d j q) _    = j
  ty  (into d j q) zero = refl
  gr  (into d j q) zero = val-≾ᵣ⁻ (≾ᵣ-trans q (·ᵣ-monoˡ-≾ᵣ (≃ᵣ⇒≿ᵣ (·ᵣ-identityˡ d))))
  dfs (into d j q)      = sym (defs-⌜⌝ (defs Γ))

  out : ∀ d i → valʳ (lookup-gr E₀ i) ≾ᵣ d → Ren ∅ᴴ (D d (lookup-ty Γ (emb i))) E₀
  pos (out d i q) _    = i
  ty  (out d i q) zero = ctx-ty i
  gr  (out d i q) zero = val-≾ᵣ⁻ (≾ᵣ-trans q (≃ᵣ⇒≿ᵣ (·ᵣ-identityˡ d)))
  dfs (out d i q)      = trans ctx-dfs (sym (defs-⌜⌝ (defs Γ)))

  up : ∀ d A → Ren ∅ᴴ (D ⊤ᵣ A) (D d A)
  pos (up d A) i    = i
  ty  (up d A) zero = refl
  gr  (up d A) zero = val-≾ᵣ⁻ (·ᵣ-monoʳ-≾ᵣ (≾-⊤ᵣ d))
  dfs (up d A)      = refl

  -- `φ` and `ψ` act on positions through `emb`

  φ-emb : ∀ {m} {Δ : OCtx ∅ˢ m} → (g : Ren ∅ᴴ Δ E₀) → ∀ x → pos (φ g) x ≡ emb (pos g x)
  φ-emb g x = trans (at (φ-cong (≐ʳ-sym (∘ʳ-identityˡ-≐ʳ g))) x) (at (φ-nat g id-ren) x)

  ψ-emb : ∀ {m} {Δ : OCtx ∅ˢ m} → (f : Ren ∅ᴴ (Δ ⟨ rconst ρ ⟩) Γ) → ∀ x
        → emb (pos (ψ f) x) ≡ pos f x
  ψ-emb f x = trans (sym (φ-emb (ψ f) x)) (at (φ∘ψ f) x)

  ψ-into : ∀ d i q → pos (ψ (into d (emb i) q)) zero ≡ i
  ψ-into d i q = at (≐ʳ-trans (≐ʳ-sym (ψ∘φ (ψ f ∘ʳ up d A)))
                              (≐ʳ-trans (ψ-cong same) (ψ∘φ s))) zero
    where
    A = lookup-ty Γ (emb i)
    f = into d (emb i) q
    s = out ⊤ᵣ i (≾-⊤ᵣ _)

    same : φ (ψ f ∘ʳ up d A) ≐ʳ φ s
    same = mk≐ʳ λ { zero → trans (φ-emb (ψ f ∘ʳ up d A) zero)
                                 (trans (ψ-emb f zero) (sym (φ-emb s zero))) }

  res⇒′ : ∀ i d → valʳ (lookup-gr E₀ i) ≾ᵣ d → valʳ (lookup-gr Γ (emb i)) ≾ᵣ d ·ᵣ ρ
  res⇒′ i d q =
    ≾ᵣ-trans (subst (λ j → valʳ (lookup-gr Γ j) ≾ᵣ (𝟏ᵣ ·ᵣ d) ·ᵣ ρ) (φ-emb s zero)
                    (val-≾ᵣ (gr (φ s) zero)))
             (·ᵣ-monoˡ-≾ᵣ (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ d)))
    where s = out d i q

  ⇒res′ : ∀ i d → valʳ (lookup-gr Γ (emb i)) ≾ᵣ d ·ᵣ ρ → valʳ (lookup-gr E₀ i) ≾ᵣ d
  ⇒res′ i d q =
    ≾ᵣ-trans (subst (λ j → valʳ (lookup-gr E₀ j) ≾ᵣ 𝟏ᵣ ·ᵣ d) (ψ-into d i q)
                    (val-≾ᵣ (gr (ψ (into d (emb i) q)) zero)))
             (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ d))

left-adjoint⇔lowering : ∀ {ρ}
  → (LeftAdjoint {∅ˢ} ∅ᴴ (rconst ρ) → ∀ {n} → (Γ : OCtx ∅ˢ n) → Lowering ρ Γ)
  × ((∀ {n} → (Γ : OCtx ∅ˢ n) → Lowering ρ Γ) → LeftAdjoint {∅ˢ} ∅ᴴ (rconst ρ))
left-adjoint⇔lowering = left-adjoint⇒lowering , lowering⇒left-adjoint

PRA⇔lowering : ∀ {ρ}
  → (PRA {∅ˢ} ∅ᴴ (rconst ρ) → ∀ {n} → (Γ : OCtx ∅ˢ n) → Lowering ρ Γ)
  × ((∀ {n} → (Γ : OCtx ∅ˢ n) → Lowering ρ Γ) → PRA {∅ˢ} ∅ᴴ (rconst ρ))
PRA⇔lowering =
    (λ pra → left-adjoint⇒lowering (PRA⇒LeftAdjoint ∅ᴴ pra))
  , (λ low → LeftAdjoint⇒PRA ∅ᴴ (lowering⇒left-adjoint low))

-- a left adjoint gives the residual of every `g ≾ ⊤ · ρ`, read off the
-- representation at `([] ∷ unit) ⟨ g ⟩` against the contexts
-- `([] ∷ unit) ⟨ d ⟩`

one : R → OCtx ∅ˢ 1
one d = ([] ∷ unit) ⟨ rconst d ⟩

one-unique : (i : Fin 1) → i ≡ zero
one-unique zero = refl

left-adjoint⇒residual : ∀ {ρ} → LeftAdjoint {∅ˢ} ∅ᴴ (rconst ρ)
                      → ∀ g → g ≾ᵣ ⊤ᵣ ·ᵣ ρ → Residual ρ g
left-adjoint⇒residual {ρ} la g p = valʳ (lookup-gr E₀ i₀) , record
  { res⇒ = res⇒′
  ; ⇒res = ⇒res′
  }
  where
  E₀ = proj₁ (proj₂ (la (one g)))
  open HomIso (proj₂ (proj₂ (la (one g))))

  -- `one g → (one d) ⟨ ρ ⟩`, given `g ≾ d · ρ`

  to : ∀ d → g ≾ᵣ d ·ᵣ ρ → Ren ∅ᴴ (one d ⟨ rconst ρ ⟩) (one g)
  pos (to d q) i = i
  ty  (to d q) zero = refl
  gr  (to d q) zero =
    val-≾ᵣ⁻ (≾ᵣ-trans (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ g))
              (≾ᵣ-trans q (·ᵣ-monoˡ-≾ᵣ (≃ᵣ⇒≿ᵣ (·ᵣ-identityˡ d)))))
  dfs (to d q) = refl

  f⊤ = to ⊤ᵣ p
  i₀ = pos (ψ f⊤) zero

  -- `one d → one ⊤`

  up : ∀ d → Ren ∅ᴴ (one ⊤ᵣ) (one d)
  pos (up d) i = i
  ty  (up d) zero = refl
  gr  (up d) zero = val-≾ᵣ⁻ (·ᵣ-monoʳ-≾ᵣ (≾-⊤ᵣ d))
  dfs (up d) = refl

  res⇒′ : ∀ d → valʳ (lookup-gr E₀ i₀) ≾ᵣ d → g ≾ᵣ d ·ᵣ ρ
  res⇒′ d q =
    ≾ᵣ-trans (≃ᵣ⇒≿ᵣ (·ᵣ-identityˡ g))
      (≾ᵣ-trans (subst (λ j → valʳ (lookup-gr (one g) j) ≾ᵣ (𝟏ᵣ ·ᵣ d) ·ᵣ ρ)
                       (one-unique (pos (φ s) zero)) (val-≾ᵣ (gr (φ s) zero)))
                (·ᵣ-monoˡ-≾ᵣ (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ d))))
    where
    s : Ren ∅ᴴ (one d) E₀
    pos s i = i₀
    ty  s zero = ty (ψ f⊤) zero
    gr  s zero = val-≾ᵣ⁻ (≾ᵣ-trans q (≃ᵣ⇒≿ᵣ (·ᵣ-identityˡ d)))
    dfs s = dfs (ψ f⊤)

  ⇒res′ : ∀ d → g ≾ᵣ d ·ᵣ ρ → valʳ (lookup-gr E₀ i₀) ≾ᵣ d
  ⇒res′ d q =
    ≾ᵣ-trans (subst (λ j → valʳ (lookup-gr E₀ j) ≾ᵣ 𝟏ᵣ ·ᵣ d) same (val-≾ᵣ (gr (ψ (to d q)) zero)))
             (≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ d))
    where
    -- `ψ (to d q) ∘ up d ≐ ψ f⊤`, as `φ` of both lands in `one g`

    same : pos (ψ (to d q)) zero ≡ i₀
    same =
      trans (sym (at (ψ∘φ (ψ (to d q) ∘ʳ up d)) zero))
        (at (ψ-cong (mk≐ʳ λ i → trans (one-unique _) (sym (one-unique _)))) zero)

PRA⇒residual : ∀ {ρ} → PRA {∅ˢ} ∅ᴴ (rconst ρ) → ∀ g → g ≾ᵣ ⊤ᵣ ·ᵣ ρ → Residual ρ g
PRA⇒residual pra = left-adjoint⇒residual (PRA⇒LeftAdjoint ∅ᴴ pra)
