--------------------------------------------------------------------------
-- The adjoints of the lock in hom-set form.                            --
--                                                                      --
-- A left adjoint of `L_ρ` at `Γ` is a context `E` with a bijection     --
-- `Ren [] E Δ ≅ Ren [] Γ (Δ ⟨ ρ ⟩)` up to `_≐ʳ_`, natural in `Δ`       --
-- (`HomIso`). It exists exactly when `(Γ ↓ L_ρ)` has an initial        --
-- object: from `(E , η)` initial, `φ g = L_ρ g ∘ η` and `ψ` takes the  --
-- unique morphism; from `φ`, `(E , φ id)` is initial                   --
-- (`left-adjoint⇔hom`). See S. Mac Lane, Categories for the Working    --
-- Mathematician, 2nd ed., Springer 1998, Chapter IV.1, Theorem 2.      --
--                                                                      --
-- A parametric right adjoint is a left adjoint of `Δ ↦ (L Δ , L !)`,   --
-- into the slice over `L []`. At `(Γ , s)` its hom-set form is a       --
-- context `E s` with `Ren [] (E s) Δ` in bijection with the `f` over   --
-- `s` (`L ! ∘ f ≐ʳ s`), natural in `Δ` (`HomIsoOver`); summed over     --
-- `s`, `Hom(Γ, L Δ) ≅ Σ (s : Γ → L []) Hom(E s, Δ)`. It is equivalent  --
-- to `PRA` (`PRA⇔hom`). See R. Street, The petit topos of globular     --
-- sets, J. Pure Appl. Algebra 154 (2000) 299-315; M. Weber, Generic    --
-- morphisms, parametric representations and weakly cartesian monads,   --
-- Theory Appl. Categ. 13 (2004) 191-234; M. Weber, Familial            --
-- 2-functors and parametric right adjoints, Theory Appl. Categ. 18     --
-- (2007) 665-732.                                                      --
--                                                                      --
-- `[] ⟨ ρ ⟩` has no variables, so every `f` lies over every `s`        --
-- (`into-[]⟨⟩-≐ʳ`) and a nonempty `(Γ ↓ L_ρ)` is connected             --
-- (`connected`): both forms reduce to the hom-set form at each `Γ`.    --
--------------------------------------------------------------------------

open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Grades.Base
open import Language.Spec

module MonomorphicCalculus.Syntax.Renaming.Lock.Adjunction (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import MonomorphicCalculus.Syntax.Contexts             S
open import MonomorphicCalculus.Syntax.Renaming             S
open import MonomorphicCalculus.Syntax.Renaming.Equivalence S
open import MonomorphicCalculus.Syntax.Renaming.Lock        S

------------------------------------------------------------------------
-- Left adjoint

-- a bijection `Ren [] E Δ ≅ Ren [] Γ (Δ ⟨ ρ ⟩)`, natural in `Δ`

record HomIso (ρ : R) (Γ E : Ctx) : Set where
  field
    φ      : ∀ {Δ} → Ren [] E Δ → Ren [] Γ (Δ ⟨ ρ ⟩)
    ψ      : ∀ {Δ} → Ren [] Γ (Δ ⟨ ρ ⟩) → Ren [] E Δ
    φ-cong : ∀ {Δ} {g g' : Ren [] E Δ} → g ≐ʳ g' → φ g ≐ʳ φ g'
    ψ-cong : ∀ {Δ} {f f' : Ren [] Γ (Δ ⟨ ρ ⟩)} → f ≐ʳ f' → ψ f ≐ʳ ψ f'
    ψ∘φ    : ∀ {Δ} → (g : Ren [] E Δ) → ψ (φ g) ≐ʳ g
    φ∘ψ    : ∀ {Δ} → (f : Ren [] Γ (Δ ⟨ ρ ⟩)) → φ (ψ f) ≐ʳ f
    φ-nat  : ∀ {Δ Δ'} → (h : Ren [] Δ Δ') → (g : Ren [] E Δ)
           → φ (h ∘ʳ g) ≐ʳ (cong-⟨⟩-ren h ∘ʳ φ g)

LeftAdjointʰ : R → Set
LeftAdjointʰ ρ = (Γ : Ctx) → Σ[ E ∈ Ctx ] HomIso ρ Γ E

-- an initial object gives the bijection

initial⇒hom : ∀ {ρ Γ} → (I : Comma ρ Γ) → Initial I → HomIso ρ Γ (ctx I)
initial⇒hom {ρ} {Γ} I init = record
  { φ      = φ
  ; ψ      = ψ
  ; φ-cong = λ e → ∘ʳ-≐ʳ (cong-⟨⟩-ren-≐ʳ e) ≐ʳ-refl
  ; ψ-cong = λ {Δ} {f} {f'} e →
      proj₂ (init (Δ ,ᵒ f')) (ψ f ,ʰ ≐ʳ-trans (tri (proj₁ (init (Δ ,ᵒ f)))) e)
  ; ψ∘φ    = λ {Δ} g → ≐ʳ-sym (proj₂ (init (Δ ,ᵒ φ g)) (g ,ʰ ≐ʳ-refl))
  ; φ∘ψ    = λ {Δ} f → tri (proj₁ (init (Δ ,ᵒ f)))
  ; φ-nat  = λ h g →
      ≐ʳ-trans (∘ʳ-≐ʳ (cong-⟨⟩-ren-∘-≐ʳ h g) ≐ʳ-refl) (∘ʳ-assoc-≐ʳ _ _ _)
  }
  where
  φ : ∀ {Δ} → Ren [] (ctx I) Δ → Ren [] Γ (Δ ⟨ ρ ⟩)
  φ g = cong-⟨⟩-ren g ∘ʳ str I

  ψ : ∀ {Δ} → Ren [] Γ (Δ ⟨ ρ ⟩) → Ren [] (ctx I) Δ
  ψ {Δ} f = map (proj₁ (init (Δ ,ᵒ f)))

-- the bijection gives an initial object, `(E , φ id)`

module _ {ρ Γ E} (H : HomIso ρ Γ E) where
  open HomIso H

  hom-object : Comma ρ Γ
  hom-object = E ,ᵒ φ id-ren

  ψ-tri : ∀ {Δ} → (f : Ren [] Γ (Δ ⟨ ρ ⟩)) → (cong-⟨⟩-ren (ψ f) ∘ʳ φ id-ren) ≐ʳ f
  ψ-tri f =
    ≐ʳ-trans (≐ʳ-sym (φ-nat (ψ f) id-ren))
      (≐ʳ-trans (φ-cong (∘ʳ-identityʳ-≐ʳ (ψ f))) (φ∘ψ f))

  hom⇒initial : Initial hom-object
  hom⇒initial X =
      (ψ (str X) ,ʰ ψ-tri (str X))
    , λ h' →
        ≐ʳ-trans (≐ʳ-sym (ψ∘φ (map h')))
          (≐ʳ-trans (ψ-cong (φ-cong (≐ʳ-sym (∘ʳ-identityʳ-≐ʳ (map h')))))
            (ψ-cong (≐ʳ-trans (φ-nat (map h') id-ren) (tri h'))))

left-adjoint⇔hom : ∀ {ρ} → (LeftAdjoint ρ → LeftAdjointʰ ρ) × (LeftAdjointʰ ρ → LeftAdjoint ρ)
left-adjoint⇔hom =
    (λ la Γ → ctx (proj₁ (la Γ)) , initial⇒hom (proj₁ (la Γ)) (proj₂ (la Γ)))
  , (λ la Γ → hom-object (proj₂ (la Γ)) , hom⇒initial (proj₂ (la Γ)))

------------------------------------------------------------------------
-- Parametric right adjoint

-- `f` lies over `s`

Over : ∀ {ρ Γ Δ} → Ren [] Γ ([] ⟨ ρ ⟩) → Ren [] Γ (Δ ⟨ ρ ⟩) → Set
Over {Δ = Δ} s f = (cong-⟨⟩-ren (!ʳ Δ) ∘ʳ f) ≐ʳ s

-- a bijection between `Ren [] E Δ` and the `f : Ren [] Γ (Δ ⟨ ρ ⟩)` over
-- `s`, natural in `Δ`

record HomIsoOver (ρ : R) (Γ : Ctx) (s : Ren [] Γ ([] ⟨ ρ ⟩)) (E : Ctx) : Set where
  field
    φ      : ∀ {Δ} → Ren [] E Δ → Ren [] Γ (Δ ⟨ ρ ⟩)
    φ-over : ∀ {Δ} → (g : Ren [] E Δ) → Over s (φ g)
    ψ      : ∀ {Δ} → (f : Ren [] Γ (Δ ⟨ ρ ⟩)) → Over s f → Ren [] E Δ
    φ-cong : ∀ {Δ} {g g' : Ren [] E Δ} → g ≐ʳ g' → φ g ≐ʳ φ g'
    ψ-cong : ∀ {Δ} {f f' : Ren [] Γ (Δ ⟨ ρ ⟩)} → (p : Over s f) → (p' : Over s f')
           → f ≐ʳ f' → ψ f p ≐ʳ ψ f' p'
    ψ∘φ    : ∀ {Δ} → (g : Ren [] E Δ) → (p : Over s (φ g)) → ψ (φ g) p ≐ʳ g
    φ∘ψ    : ∀ {Δ} → (f : Ren [] Γ (Δ ⟨ ρ ⟩)) → (p : Over s f) → φ (ψ f p) ≐ʳ f
    φ-nat  : ∀ {Δ Δ'} → (h : Ren [] Δ Δ') → (g : Ren [] E Δ)
           → φ (h ∘ʳ g) ≐ʳ (cong-⟨⟩-ren h ∘ʳ φ g)

PRAʰ : R → Set
PRAʰ ρ = (Γ : Ctx) → (s : Ren [] Γ ([] ⟨ ρ ⟩)) → Σ[ E ∈ Ctx ] HomIsoOver ρ Γ s E

-- every `f` lies over every `s`

over : ∀ {ρ Γ Δ} → (s : Ren [] Γ ([] ⟨ ρ ⟩)) → (f : Ren [] Γ (Δ ⟨ ρ ⟩)) → Over s f
over s f = into-[]⟨⟩-≐ʳ _ _

hom⇒over : ∀ {ρ Γ E} → (s : Ren [] Γ ([] ⟨ ρ ⟩)) → HomIso ρ Γ E → HomIsoOver ρ Γ s E
hom⇒over s H = record
  { φ      = φ
  ; φ-over = λ g → over s (φ g)
  ; ψ      = λ f _ → ψ f
  ; φ-cong = φ-cong
  ; ψ-cong = λ _ _ → ψ-cong
  ; ψ∘φ    = λ g _ → ψ∘φ g
  ; φ∘ψ    = λ f _ → φ∘ψ f
  ; φ-nat  = φ-nat
  }
  where open HomIso H

over⇒hom : ∀ {ρ Γ E} {s : Ren [] Γ ([] ⟨ ρ ⟩)} → HomIsoOver ρ Γ s E → HomIso ρ Γ E
over⇒hom {s = s} H = record
  { φ      = φ
  ; ψ      = λ f → ψ f (over s f)
  ; φ-cong = φ-cong
  ; ψ-cong = ψ-cong (over s _) (over s _)
  ; ψ∘φ    = λ g → ψ∘φ g (over s (φ g))
  ; φ∘ψ    = λ f → φ∘ψ f (over s f)
  ; φ-nat  = φ-nat
  }
  where open HomIsoOver H

PRA⇔hom : ∀ {ρ} → (PRA ρ → PRAʰ ρ) × (PRAʰ ρ → PRA ρ)
PRA⇔hom {ρ} = to , from
  where
  to : PRA ρ → PRAʰ ρ
  to pra Γ s =
    ctx I , hom⇒over s (initial⇒hom I (λ X → proj₂ (proj₂ (pra Γ ([] ,ᵒ s))) X (connected I X)))
    where
    I = proj₁ (pra Γ ([] ,ᵒ s))

  from : PRAʰ ρ → PRA ρ
  from pra Γ X =
    hom-object H , fwd (proj₁ (hom⇒initial H X)) here , λ Y _ → hom⇒initial H Y
    where
    H = over⇒hom (proj₂ (pra Γ (cong-⟨⟩-ren (!ʳ (ctx X)) ∘ʳ str X)))
