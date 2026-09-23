------------------------------------------------------------------
-- The solver: solve, then report                                 --
--                                                                --
-- `solveOn` runs the driver and reads its residual back as a     --
-- hypothesis set, deciding the atoms no unknown affects          --
-- (`Closed`): one that holds is dropped, one that fails refuses. --
-- It instantiates `TypeInference.Solver.Solver`.                 --
-- Principality is unguarded; refutation is guarded by `NoRig`,   --
-- since at a rigid binder a failure can be a failure of          --
-- `Normal`'s decision procedures, and is stated against          --
-- satisfiable hypothesis sets.                                   --
--                                                                --
-- `reportOn` reports a solution: the residue with its var-rule   --
-- disjunctions settled, its repeated hypotheses dropped, the     --
-- unknowns its own hypotheses fix eliminated from it and from    --
-- the reported type, every grade expression in product normal    --
-- form, its disjunctions settled again, every subtyping atom and --
-- grade ordering entailed by the others kept dropped, and the    --
-- report stated over the variables occurring in it. The unknowns --
-- of the image of the caller's variables are neither eliminated  --
-- nor dropped.                                                   --
--                                                                --
-- `infer` is the reference entry point: a report on the          --
-- constraint of a term in a context is a principal typing.       --
------------------------------------------------------------------

open import Data.List.Base using (List; [])
open import Data.Maybe.Base using (Maybe; just; nothing)
import Data.Maybe.Base as Maybe
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

import TypeInference.OpenSyntax.Hyps as H

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.SolverImpl
  (S : LanguageSpec)
  (opEnum : OpEnum S)
  (umin?ᵣ : Maybe (H.UnitMinᵣ S))
  (umin?ₑ : Maybe (H.UnitMinₑ S))
  where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S using (Satisfiable; Satisfiable-⨟; _⊨ᴴ_)
open import TypeInference.OpenSyntax.Language  S

open import TypeInference.Raw.Syntax S using (RawC)
open import TypeInference.Raw.Subst  S using (_[_]ᴿᶜ; [≐]ᴿᶜ)
open import TypeInference.Erase      S using (⌊_⌋ᶜ)
open import TypeInference.Soundness  S using (ctx-substᶜ; ⌊ctxᶜ⌋; ⌊c⌋)

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S
open import TypeInference.Constraints.Properties   S using (⊨-resp-≐ˢ; ⊨-mono)

open import TypeInference.Principality      S
open import TypeInference.Solver.Fragment   S
open import TypeInference.Solver            S

open import TypeInference.SolverImpl.Core.Unify    S using (Rig; _∈ᶠ_)
open import TypeInference.SolverImpl.Core.UnifyMGU S using (Fixing; fixing)

open import TypeInference.SolverImpl.Resid     S
open import TypeInference.SolverImpl.Closed    S using (closedᴴ; closedᴴ-⊩; closedᴴ-⊆; closedᴴ-fail)
open import TypeInference.SolverImpl.State     S
open import TypeInference.SolverImpl.Solve     S opEnum umin?ᵣ umin?ₑ
open import TypeInference.SolverImpl.Principal S opEnum umin?ᵣ umin?ₑ
open import TypeInference.SolverImpl.Simplify  S umin?ᵣ umin?ₑ
  using (simplify; simplify-⊩; simplify-⊨; trimElim; memʳ?; memᵉ?)
open import TypeInference.SolverImpl.Normal    S umin?ᵣ umin?ₑ using (decide≾ᵣ; decide≾ₑ)
open import TypeInference.SolverImpl.Eliminate S
  using (Elim; Elimᶠ; Entails; entails; eliminate; _⨾ᴱ_)
open import TypeInference.SolverImpl.Canon     S umin?ᵣ umin?ₑ using (canonElim)
open import TypeInference.SolverImpl.Vars       S using (Vars; ⊆-refl; fvˢ; Fixes; fixes-id; fixes-⨟)
open import TypeInference.SolverImpl.Strengthen S
  using (Ren; Strengthened; strengthen; ⌜_⌝ʳ; _[_]ᴴ; ⊩ᴴ-ren⁺; fixes-≐; conv⁻; inst⁻; keep⁻; princ⁻)

Fixing-[] : ∀ {Θ Ψ} → (σ : Subst Θ Ψ) → Fixing [] σ
Fixing-[] σ = fixing (λ i ()) (λ i i' ())

solveOn : ∀ {Θ} → Constraint Θ
        → Maybe (Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ'))
solveOn C with solve init C
... | nothing = nothing
... | just (s' , m , w) with reexpand s'
...   | nothing = nothing
...   | just (s₂ , m₂) with toHyps (res s₂)
...     | nothing        = nothing
...     | just (Q₀ , hq) with closedᴴ Q₀
...       | nothing = nothing
...       | just Q  = just (Ψ s₂ , θ s₂ , Q)

solveOn-sound : ∀ {Θ} → (C : Constraint Θ)
              → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
              → solveOn C ≡ just (Θ' , σ , Q)
              → σ ⊨[ Q ] C
solveOn-sound C eq with solve init C in e
... | nothing = ⊥just eq
... | just (s' , m , w) with reexpand s' in e₂
...   | nothing = ⊥just eq
...   | just (s₂ , m₂) with toHyps (res s₂) in e'
...     | nothing = ⊥just eq
...     | just (Q₀ , hq) with closedᴴ Q₀ in e''
...       | nothing = ⊥just eq
...       | just Q₁ with eq
...         | refl =
              ⊨-resp-≐ˢ (⨟-idʳ (θ s₂)) C
                (⊨-mono (closedᴴ-⊩ Q₀ e'') C
                  (⊨-resp-≐ˢ (⨟-idʳ (θ s₂)) C (wit-mono m₂ C w idˢ Q₀ hq)))

solveOn-complete : ∀ {Θ} → (C : Constraint Θ) → NoRig C
                 → solveOn C ≡ nothing
                 → ∀ {Θ'} → (σ : Subst Θ Θ') → (Q : Hyps Θ') → Satisfiable Q
                 → ¬ (σ ⊨[ Q ] C)
solveOn-complete C nr eq σ Q sQ sat with solve init C in e
... | nothing = solve-fail init C nr e σ Q (Fixing-[] σ) ⊩ᴿ-empty sat
... | just (s' , m , w) with reexpand s' in e₂
...   | nothing =
        reexpand-fail s' e₂ (proj₁ fac) Q (proj₁ (proj₂ (proj₂ fac)))
  where
    fac = solve-principal init C e σ Q sat ⊩ᴿ-empty
...   | just (s₂ , m₂) with toHyps (res s₂) in e'
...     | just (Q₀ , hq) with closedᴴ Q₀ in e''
...       | just _  = ⊥nothing eq
...       | nothing =
            closedᴴ-fail Q₀ e''
              (Satisfiable-⨟ (toHyps-compl (res s₂) e' (proj₁ fac₂) (proj₂ (proj₂ fac₂))) sQ)
  where
    fac  = solve-principal init C e σ Q sat ⊩ᴿ-empty
    fac₂ = reexpand-princ s' e₂ (proj₁ fac) Q (proj₁ (proj₂ (proj₂ fac)))
solveOn-complete C nr eq σ Q sQ sat | just (s' , m , w) | just (s₂ , m₂) | nothing
  with toHyps-nothing (res s₂) e'
...       | inj₁ (A , mem , q) =
            etDec-refute A q (proj₁ fac₂) (⊩ts (proj₂ (proj₂ fac₂)) mem)
  where
    fac  = solve-principal init C e σ Q sat ⊩ᴿ-empty
    fac₂ = reexpand-princ s' e₂ (proj₁ fac) Q (proj₁ (proj₂ (proj₂ fac)))
...       | inj₂ (A , B , mem , q) =
            ⊥nothing (trans (sym (proj₂ (reexpand-dec s' e₂ mem))) q)

solveOn-principal : ∀ {Θ} → (C : Constraint Θ)
                  → {Θ⁺ : Scope} {σ⁺ : Subst Θ Θ⁺} {Q⁺ : Hyps Θ⁺}
                  → solveOn C ≡ just (Θ⁺ , σ⁺ , Q⁺)
                  → ∀ {Θ''} → (σ : Subst Θ Θ'') → (Q : Hyps Θ'')
                  → σ ⊨[ Q ] C
                  → Σ[ δ ∈ Subst Θ⁺ Θ'' ]
                      (((σ⁺ ⨟ˢ δ) ≐ˢ σ) × (Q ⊩ᴴ Q⁺ [ δ ]))
solveOn-principal C eq σ Q sat with solve init C in e
... | nothing = ⊥just eq
... | just (s' , m , w) with reexpand s' in e₂
...   | nothing = ⊥just eq
...   | just (s₂ , m₂) with toHyps (res s₂) in e'
...     | nothing = ⊥just eq
...     | just (Q₀ , hq) with closedᴴ Q₀ in e''
...       | nothing = ⊥just eq
...       | just Q₁ with eq
...         | refl = δ₂ , tri , closedᴴ-⊆ Q₀ e'' (toHyps-compl (res s₂) e' δ₂ h₂)
  where
    fac  = solve-principal init C e σ Q sat ⊩ᴿ-empty
    δ    = proj₁ fac
    tri₁ = proj₁ (proj₂ fac)
    hres = proj₁ (proj₂ (proj₂ fac))

    fac₂ = reexpand-princ s' e₂ δ Q hres
    δ₂   = proj₁ fac₂
    tri₂ = proj₁ (proj₂ fac₂)
    h₂   = proj₂ (proj₂ fac₂)

    tri = ≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m₂)) δ₂)
          (≐ˢ-trans (⨟-assoc (θ s') (mδ m₂) δ₂)
          (≐ˢ-trans (⨟-congʳ (θ s') tri₂)
          (≐ˢ-trans (⨟-congˡ (≐ˢ-sym (mtri m)) δ) tri₁)))

solver : Solver NoRig (λ _ → ⊤)
solver = record
  { solve           = solveOn
  ; solve-sound     = solveOn-sound
  ; solve-complete  = solveOn-complete
  ; solve-principal = λ C _ → solveOn-principal C
  }

-- The entailment test of elimination by equality: an ordering among
-- the hypotheses, or one `decide≾` proves from them

entailsᴴ : Entails
entailsᴴ = entails entᵣ? entₑ?
  where
    entᵣ? : ∀ {Θ} → (Q : Hyps Θ) → (ρ ρ' : RExp Θ) → Maybe (Q ⊩ ρ ≾̂ᵣ ρ')
    entᵣ? Q ρ ρ' with memʳ? (ρ , ρ') (ordᵣ Q)
    ... | just m  = just (hypᵣ m)
    ... | nothing = decide≾ᵣ ρ ρ'

    entₑ? : ∀ {Θ} → (Q : Hyps Θ) → (ε ε' : EExp Θ) → Maybe (Q ⊩ ε ≾̂ₑ ε')
    entₑ? Q ε ε' with memᵉ? (ε , ε') (ordₑ Q)
    ... | just m  = just (hypₑ m)
    ... | nothing = decide≾ₑ ε ε'

-- A solution, its residue as the solver returns it, and the residue
-- simplified, which entails the residue and holds at each of its
-- closed instances. The unknowns the simplified residue fixes are then
-- eliminated from it and from the reported type `X` by a substitution
-- `η`: the reported type is `X` along `η` up to convertibility, the
-- reported hypotheses entail the simplified residue along `η`, each
-- closed instance of the simplified residue is one of them, and there
-- the reported type is a subtype of `X`. Normalisation of the grade
-- expressions and `trim` run as the last two elimination steps.
--
-- The report is relative to the caller's variables `w`: `η` fixes the
-- unknowns of their image. It is stated over the scope `Θ̃` of the
-- variables occurring in it or in that image, embedded in the
-- solution's by the renaming `ι`, the caller's variables instantiated
-- by `σ̃`; an instance of `Θ̃` extends along `ι`.

record Reported {Θ₀ Θ : Scope} (w : Subst Θ₀ Θ) (X : OCType Θ) (C : Constraint Θ) : Set where
  constructor report
  field
    Θ'     : Scope
    σ      : Subst Θ Θ'
    Q      : Hyps Θ'
    Q̂      : Hyps Θ'
    Θ̃      : Scope
    ι      : Ren Θ̃ Θ'
    σ̃      : Subst Θ₀ Θ̃
    X̃      : OCType Θ̃
    Q̃      : Hyps Θ̃
    η      : Subst Θ' Θ'
    solved : solveOn C ≡ just (Θ' , σ , Q)
    to-Q̂   : Q ⊨ᴴ Q̂
    to-Q   : Q̂ ⊩ᴴ Q
    fix    : w ⨟ˢ σ ⨟ˢ η ≐ˢ w ⨟ˢ σ
    σ̃-ι    : σ̃ ⨟ˢ ⌜ ι ⌝ʳ ≐ˢ w ⨟ˢ σ
    conv   : X̃ [ ⌜ ι ⌝ʳ ]ᶜ ≡̂ᶜ X [ σ ]ᶜ [ η ]ᶜ
    inst   : Q̃ [ ι ]ᴴ ⊩ᴴ Q̂ [ η ]
    to-Q̃   : (δ : Subst Θ' ∅ˢ) → ∅ᴴ ⊩ᴴ Q̂ [ δ ] → ∅ᴴ ⊩ᴴ Q̃ [ ⌜ ι ⌝ʳ ⨟ˢ δ ]
    princ  : (δ : Subst Θ' ∅ˢ) → ∅ᴴ ⊩ᴴ Q̂ [ δ ]
           → ∅ᴴ ∣ X̃ [ ⌜ ι ⌝ʳ ⨟ˢ δ ]ᶜ <:̂ᶜ X [ σ ]ᶜ [ δ ]ᶜ
    ext-ι  : ∀ {Ψ} → (δ : Subst Θ̃ Ψ) → Σ[ δ' ∈ Subst Θ' Ψ ] (⌜ ι ⌝ʳ ⨟ˢ δ' ≐ˢ δ)

-- The report of what `solveOn` returns

reportOf : ∀ {Θ₀ Θ} → (w : Subst Θ₀ Θ) → (X : OCType Θ) → (C : Constraint Θ)
         → (s : Maybe (Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ'))) → solveOn C ≡ s
         → Maybe (Reported w X C)
reportOf w X C nothing           e = nothing
reportOf w X C (just (Θ' , σ , Q)) e =
      just (report Θ' σ Q (simplify Q) (Θ⁻ sr) (ι sr) (τ⁻ sr) (X⁻ sr) (Q⁻ sr) (Elim.η el)
                   e (simplify-⊨ Q) (simplify-⊩ Q) (fixes-≐ fx (w ⨟ˢ σ) ⊆-refl) (τ-ι sr)
                   (conv⁻ el sr) (inst⁻ el sr) (keep⁻ el sr) (princ⁻ el sr) (ext-ι sr))
  where
    open Strengthened

    F : Vars Θ'
    F = fvˢ (w ⨟ˢ σ)

    el₀ : Elimᶠ F (X [ σ ]ᶜ) (simplify Q)
    el₀ = eliminate entailsᴴ F (X [ σ ]ᶜ) (simplify Q)

    el : Elim (X [ σ ]ᶜ) (simplify Q)
    el = proj₁ el₀ ⨾ᴱ canonElim _ _ ⨾ᴱ trimElim _ _

    fx : Fixes F (Elim.η el)
    fx = fixes-⨟ (fixes-⨟ (proj₂ el₀) fixes-id) fixes-id

    sr : Strengthened (w ⨟ˢ σ) (Elim.Ĉ el) (Elim.Q̂ el)
    sr = strengthen (w ⨟ˢ σ) (Elim.Ĉ el) (Elim.Q̂ el)

reportOn : ∀ {Θ₀ Θ} → (w : Subst Θ₀ Θ) → (X : OCType Θ) → (C : Constraint Θ)
         → Maybe (Reported w X C)
reportOn w X C = reportOf w X C (solveOn C) refl

-- A report fails only where the solver does

reportOf-nothing : ∀ {Θ₀ Θ} {w : Subst Θ₀ Θ} {X : OCType Θ} {C : Constraint Θ} {Y : Set}
                 → (f : Reported w X C → Y)
                 → (s : Maybe (Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ'))) → (e : solveOn C ≡ s)
                 → Maybe.map f (reportOf w X C s e) ≡ nothing → s ≡ nothing
reportOf-nothing f nothing  e eq = refl
reportOf-nothing f (just _) e eq = ⊥nothing eq

------------------------------------------------------------------------
-- The reference entry point
--
-- A report on the constraint of `M` in `Γ`, relative to the program's
-- variables, is a principal typing of `M` in `Γ`: its derivation is the
-- principal one instantiated along `η` and retracted along `ι`, and a
-- typing factors through the principal one and then through the report
-- at each closed instance.

typing : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n)
       → Reported wk₊ (X̂ Θ ‼ t̂ Θ) C[ Γ , M ] → PrincipalTyping Γ M
typing {Θ} Γ M r = mkPrincipalTyping Θ̃ σ̃ Q̃ X̃ D̃ ⌊D̃⌋ inst' fac
  where
    open Reported r

    X : OCType (Θ +ty +e)
    X = X̂ Θ ‼ t̂ Θ

    p : Principal Γ M
    p = principal solver Γ M tt solved

    -- a retraction of `ι`

    π : Subst Θ' Θ̃
    π = proj₁ (ext-ι idˢ)

    πι : ⌜ ι ⌝ʳ ⨟ˢ π ≐ˢ idˢ
    πι = proj₂ (ext-ι idˢ)

    -- the reported hypotheses entail the residue along `η` and `π`

    hQ : Q̃ ⊩ᴴ Q [ η ⨟ˢ π ]
    hQ = ⊩ᴴ-⨟ (⊩ᴴ-ren⁺ ι (⊩ᴴ-≐ (≐ˢ-sym πι) ⊩ᴴ-refl)) (⊩ᴴ-⨟ inst to-Q)

    -- the program's variables follow

    ctx : ∀ {Θ''} → (δ : Subst Θ̃ Θ'') → wk₊ ⨟ˢ (σ ⨟ˢ (η ⨟ˢ π ⨟ˢ δ)) ≐ˢ σ̃ ⨟ˢ δ
    ctx δ =
      ≐ˢ-trans (≐ˢ-sym (⨟-assoc wk₊ σ (η ⨟ˢ π ⨟ˢ δ)))
      (≐ˢ-trans (≐ˢ-sym (⨟-assoc (wk₊ ⨟ˢ σ) (η ⨟ˢ π) δ))
      (⨟-congˡ
        (≐ˢ-trans (≐ˢ-sym (⨟-assoc (wk₊ ⨟ˢ σ) η π))
        (≐ˢ-trans (⨟-congˡ fix π)
        (≐ˢ-trans (⨟-congˡ (≐ˢ-sym σ̃-ι) π)
        (≐ˢ-trans (⨟-assoc σ̃ ⌜ ι ⌝ʳ π)
        (≐ˢ-trans (⨟-congʳ σ̃ πι) (⨟-idʳ σ̃))))))
        δ))

    -- and so does the type, up to convertibility

    ty : ∀ {Θ''} → (δ : Subst Θ̃ Θ'') → X [ σ ⨟ˢ (η ⨟ˢ π ⨟ˢ δ) ]ᶜ ≡̂ᶜ X̃ [ δ ]ᶜ
    ty δ =
      subst₂ _≡̂ᶜ_ eqL eqR (≡̂ᶜ-subst δ (≡̂ᶜ-subst π (≡̂ᶜ-sym conv)))
      where
        eqL : X [ σ ]ᶜ [ η ]ᶜ [ π ]ᶜ [ δ ]ᶜ ≡ X [ σ ⨟ˢ (η ⨟ˢ π ⨟ˢ δ) ]ᶜ
        eqL = trans (cong (_[ δ ]ᶜ) ([⨟]ᶜ (X [ σ ]ᶜ) η π))
              (trans ([⨟]ᶜ (X [ σ ]ᶜ) (η ⨟ˢ π) δ) ([⨟]ᶜ X σ (η ⨟ˢ π ⨟ˢ δ)))

        eqR : X̃ [ ⌜ ι ⌝ʳ ]ᶜ [ π ]ᶜ [ δ ]ᶜ ≡ X̃ [ δ ]ᶜ
        eqR = cong (_[ δ ]ᶜ) (trans ([⨟]ᶜ X̃ ⌜ ι ⌝ʳ π) (trans ([≐]ᶜ πι X̃) ([id]ᶜ X̃)))

    inst' : ∀ {Θ''} → (δ : Subst Θ̃ Θ'') → (Q' : Hyps Θ'') → Q' ⊩ᴴ Q̃ [ δ ]
          → Σ[ D ∈ (Q' ∣ Γ [ σ̃ ⨟ˢ δ ]ᶜᵗˣ ⊢C⦂ X̃ [ δ ]ᶜ) ] (⌊ D ⌋ᶜ ≡ M [ σ̃ ⨟ˢ δ ]ᴿᶜ)
    inst' δ Q' h =
      subC (ctx-substᶜ ceq D) (≡̂ᶜ-<:̂ (ty δ)) , trans (⌊ctxᶜ⌋ ceq D) (trans e meq)
      where
        τ = η ⨟ˢ π ⨟ˢ δ
        i = Principal.instantiate p τ Q' (⊩ᴴ-⨟ h hQ)
        D = proj₁ i
        e = proj₂ i

        ceq : Γ₊ Γ [ σ ⨟ˢ τ ]ᶜᵗˣ ≡ Γ [ σ̃ ⨟ˢ δ ]ᶜᵗˣ
        ceq = trans (Γ₊-[] Γ (σ ⨟ˢ τ)) ([≐]ᶜᵗˣ (ctx δ) Γ)

        meq : M₊ M [ σ ⨟ˢ τ ]ᴿᶜ ≡ M [ σ̃ ⨟ˢ δ ]ᴿᶜ
        meq = trans (M₊-[] M (σ ⨟ˢ τ)) ([≐]ᴿᶜ (ctx δ) M)

    i₀ = inst' idˢ Q̃ ⊩ᴴ-refl

    D̃ : Q̃ ∣ Γ [ σ̃ ]ᶜᵗˣ ⊢C⦂ X̃
    D̃ = c-subst ([id]ᶜ X̃) (ctx-substᶜ ([≐]ᶜᵗˣ (⨟-idʳ σ̃) Γ) (proj₁ i₀))

    ⌊D̃⌋ : ⌊ D̃ ⌋ᶜ ≡ M [ σ̃ ]ᴿᶜ
    ⌊D̃⌋ = trans (⌊c⌋ ([id]ᶜ X̃) _)
           (trans (⌊ctxᶜ⌋ ([≐]ᶜᵗˣ (⨟-idʳ σ̃) Γ) (proj₁ i₀))
           (trans (proj₂ i₀) ([≐]ᴿᶜ (⨟-idʳ σ̃) M)))

    fac : ∀ {Θ''} → (σ₀ : Subst Θ Θ'') → (Q₀ : Hyps Θ'') → {C₀ : OCType Θ''}
        → (D₀ : Q₀ ∣ Γ [ σ₀ ]ᶜᵗˣ ⊢C⦂ C₀) → ⌊ D₀ ⌋ᶜ ≡ M [ σ₀ ]ᴿᶜ
        → (δ₀ : Subst Θ'' ∅ˢ) → ∅ᴴ ⊩ᴴ Q₀ [ δ₀ ]
        → Σ[ δ ∈ Subst Θ̃ ∅ˢ ]
            ((σ̃ ⨟ˢ δ ≐ˢ σ₀ ⨟ˢ δ₀) × (∅ᴴ ⊩ᴴ Q̃ [ δ ]) × (∅ᴴ ∣ X̃ [ δ ]ᶜ <:̂ᶜ C₀ [ δ₀ ]ᶜ))
    fac σ₀ Q₀ {A₀ ‼ ε₀} D₀ e₀ δ₀ h₀ =
      ⌜ ι ⌝ʳ ⨟ˢ δ' , agree , to-Q̃ δ' hQ̂ , <:̂ᶜ-trans (princ δ' hQ̂) below
      where
        pi = principal-inst p σ₀ Q₀ D₀ e₀
        δ₁ = proj₁ pi
        ceq₁ = proj₁ (proj₂ pi)
        aeq = proj₁ (proj₂ (proj₂ pi))
        le = proj₁ (proj₂ (proj₂ (proj₂ pi)))
        hq = proj₂ (proj₂ (proj₂ (proj₂ pi)))

        δ' : Subst Θ' ∅ˢ
        δ' = δ₁ ⨟ˢ δ₀

        hQ̂ : ∅ᴴ ⊩ᴴ Q̂ [ δ' ]
        hQ̂ = to-Q̂ δ' (⊩ᴴ-⨟ h₀ hq)

        agree : σ̃ ⨟ˢ (⌜ ι ⌝ʳ ⨟ˢ δ') ≐ˢ σ₀ ⨟ˢ δ₀
        agree =
          ≐ˢ-trans (≐ˢ-sym (⨟-assoc σ̃ ⌜ ι ⌝ʳ δ'))
          (≐ˢ-trans (⨟-congˡ σ̃-ι δ')
          (≐ˢ-trans (≐ˢ-sym (⨟-assoc (wk₊ ⨟ˢ σ) δ₁ δ₀)) (⨟-congˡ ceq₁ δ₀)))

        below : ∅ᴴ ∣ X [ σ ]ᶜ [ δ' ]ᶜ <:̂ᶜ (A₀ ‼ ε₀) [ δ₀ ]ᶜ
        below =
          subst₂ (λ A t → ∅ᴴ ∣ A ‼ t <:̂ᶜ A₀ [ δ₀ ]ᵛ ‼ ε₀ [ δ₀ ]ᵉ)
                 (trans (cong (_[ δ₀ ]ᵛ) (sym aeq)) ([⨟]ᵛ (X̂ Θ [ σ ]ᵛ) δ₁ δ₀))
                 ([⨟]ᵉ (t̂ Θ [ σ ]ᵉ) δ₁ δ₀)
                 (<:̂ᵛ-refl (A₀ [ δ₀ ]ᵛ) ‼ₛ ⊩-substₑ h₀ le)

infer : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → Maybe (PrincipalTyping Γ M)
infer {Θ} Γ M = Maybe.map (typing Γ M) (reportOn wk₊ (X̂ Θ ‼ t̂ Θ) C[ Γ , M ])

-- Where no rigid binder occurs in the constraint of `M`, inference
-- fails only on a term no typing of which has satisfiable hypotheses

infer-fails : ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC Θ n) → NoRig C[ Γ , M ]
            → infer Γ M ≡ nothing
            → ∀ {Θ''} → (σ₀ : Subst Θ Θ'') → (Q₀ : Hyps Θ'') → {C₀ : OCType Θ''}
            → (D₀ : Q₀ ∣ Γ [ σ₀ ]ᶜᵗˣ ⊢C⦂ C₀) → ⌊ D₀ ⌋ᶜ ≡ M [ σ₀ ]ᴿᶜ
            → ¬ Satisfiable Q₀
infer-fails {Θ} Γ M nr eq σ₀ Q₀ {A₀ ‼ ε₀} D₀ e₀ sQ =
  solveOn-complete C[ Γ , M ] nr
    (reportOf-nothing (typing Γ M) (solveOn C[ Γ , M ]) refl eq)
    (σ₀ ,ᵗ A₀ ,ᵉ ε₀) Q₀ sQ (typing-sat σ₀ D₀ e₀)
