------------------------------------------------------------------
-- The grounding theorem                                          --
--                                                                --
-- A mirrored derivation, read under any grounding that satisfies  --
-- its hypothesis set, is a derivation of the original language:   --
--                                                                --
--     θ ⊨ᴴ Q  →  Q ∣ Γ ⊢C⦂ C  →  ⟦ Γ ⟧θ ⊢C⦂ ⟦ C ⟧θ               --
--                                                                --
-- This is the sole bridge back to `Syntax.Language`, and the      --
-- design check on the mirrored rules: every grade and lock of     --
-- every rule grounds definitionally. The only transports are      --
-- along the round-trip of the *ground-type* embedding `⌜_⌝ᵍ`      --
-- (`perform`, `handle`) and along the collapse of the clause      --
-- family's effect-scope weakening (`handle`).                     --
------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Open.GroundingTheorem (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts S
open import Syntax.Language S
open import Syntax.Types    S

open import TypeInference.Open.Grades    S
open import TypeInference.Open.Types     S
open import TypeInference.Open.Contexts  S
open import TypeInference.Open.Hyps      S
open import TypeInference.Open.Language  S
open import TypeInference.Open.Grounding S

mutual

  groundV : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {A : OVType Θ}
          → (θ : Grounding Θ) → θ ⊨ᴴ Q → Q ∣ Γ ⊢V⦂ A
          --------------------------------------------
          → ⟦ Γ ⟧ᶜᵗˣ θ ⊢V⦂ ⟦ A ⟧ᵛ θ

  -- The membership witness and the original's grade premise are read off
  -- `VarOK` together.

  groundV θ h (var x ok) with ground-var θ h x ok
  ... | f , y = var f y
  groundV θ h (const B c) = const c
  groundV θ h ⋆           = ⋆
  groundV θ h true        = true
  groundV θ h false       = false
  groundV θ h ⦉ V , W ⦊    = ⦉ groundV θ h V , groundV θ h W ⦊
  groundV θ h (lam M)     = lam (groundC θ h M)
  groundV θ h (subV V p)  = subV (groundV θ h V) (ground-<:ᵛ h p)

  groundC : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {C : OCType Θ}
          → (θ : Grounding Θ) → θ ⊨ᴴ Q → Q ∣ Γ ⊢C⦂ C
          --------------------------------------------
          → ⟦ Γ ⟧ᶜᵗˣ θ ⊢C⦂ ⟦ C ⟧ᶜ θ

  groundC θ h (return V) =
    return (groundV θ h V)
  groundC θ h (M ⨟ N) =
    groundC θ h M ⨟ groundC θ h N
  groundC θ h (V · W) =
    groundV θ h V · groundV θ h W
  groundC θ h (match V `in M) =
    match groundV θ h V `in groundC θ h M
  groundC θ h (absurd V) =
    absurd (groundV θ h V)
  groundC θ h (if V `then M `else N) =
    if groundV θ h V `then groundC θ h M `else groundC θ h N

  -- The parameter and arity types are the only place where a mirrored rule
  -- names a *ground* type: `⟦ ⌜ G ⌝ᵍ ⟧θ ≡ type-of-gtype G` holds by induction
  -- on `G`, not by computation, so the two premises are transported.

  groundC {Γ = Γ} θ h (perform {A} {ε} op V M) =
    perform op
      (subst (λ A₀ → ⟦ Γ ⟧ᶜᵗˣ θ ⊢V⦂ A₀)
             (⌜⌝ᵍ-ground (param op))
             (groundV θ h V))
      (subst (λ A₀ → ⟦ Γ ⟧ᶜᵗˣ θ ⟨ mapᵉ (op-grade op) ⟩ ∷ A₀
                       ⊢C⦂ ⟦ A ⟧ᵛ θ ‼ ⟦ ε ⟧ᵉ θ)
             (⌜⌝ᵍ-ground (arity op))
             (groundC θ h M))

  groundC θ h (delay τ M) =
    delay τ (groundC θ h M)

  -- The original quantifies its clause family over the continuation grade;
  -- the mirror types the clauses once against a rigid effect-grade variable.
  -- Grounding instantiates that variable, one clause per `ε''`.

  groundC θ h (handle M `with H `in N) =
    handle (groundC θ h M)
      `with (λ op ε'' → ground-clause θ h op ε'' (H op))
      `in (groundC θ h N)

  groundC θ h (unbox x ok p N) with ground-unbox θ h x ok
  ... | le , y = unbox y le (ground-<:ᵛ h p) (groundC θ h N)
  groundC θ h (box ρ V N) =
    box (groundV θ h V) (groundC θ h N)
  groundC θ h (subC M p) =
    subC (groundC θ h M) (ground-<:ᶜ h p)

  -- One operation clause, at one continuation grade. The clause derivation
  -- lives at the extended scope `Θ +e`; grounding it at `θ ,ᵍᵉ ε''` sends the
  -- rigid variable to `ε''`, definitionally. What remains is the weakening
  -- collapse and the two ground-type round-trips.

  ground-clause : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {B : OVType Θ}
                → (θ : Grounding Θ) → θ ⊨ᴴ Q
                → (op : Op) → (ε'' : E)
                → (wkᵉ-H Q ∣ wkᵉ-ctx Γ ⟨ rconst ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                               ∷ [ rconst (mapᵉ (op-grade op)) ]
                                   (⌜ arity op ⌝ᵍ ⇒ wkᵉ-v B ‼ evar (newᵉ {Θ}))
                     ⊢C⦂ wkᵉ-v B ‼ (econst (op-grade op) ·̂ₑ evar (newᵉ {Θ})))
                ---------------------------------------------------------------
                → (⟦ Γ ⟧ᶜᵗˣ θ) ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                    ∷ [ mapᵉ (op-grade op) ]
                        (type-of-gtype (arity op) ⇒ ⟦ B ⟧ᵛ θ ‼ ε'')
                  ⊢C⦂ ⟦ B ⟧ᵛ θ ‼ (op-grade op ·ₑ ε'')

  ground-clause {Γ = Γ} {B} θ h op ε'' X =
    subst₂ _⊢C⦂_
           (cong₂ _∷_
                  (cong₂ _∷_ (cong (_⟨ ⊤ᵣ ⟩) (ground-wkᵉ-ctx Γ))
                             (⌜⌝ᵍ-ground (param op)))
                  (cong₂ (λ A₀ B₀ → [ mapᵉ (op-grade op) ] (A₀ ⇒ B₀ ‼ ε''))
                         (⌜⌝ᵍ-ground (arity op))
                         (ground-wkᵉ-v B)))
           (cong (_‼ (op-grade op ·ₑ ε'')) (ground-wkᵉ-v B))
           (groundC (θ ,ᵍᵉ ε'') (⊨ᴴ-wkᵉ-ground h) X)

-- Sanity checks: the grounded derivations compute.

private

  ∅ᶜ : OCtx ∅ˢ 0
  ∅ᶜ = []

  -- The unique grounding of the empty scope

  θ₀ : Grounding ∅ˢ
  θ₀ = grounding (λ ()) (λ ()) (λ ())

  -- A variable used across a clause barrier grounds behind the `⊤ᵣ` lock

  ex-var-barrier : ∅ᴴ ∣ ((∅ᶜ ∷ Unit) ⟨ rconst ⊤ᵣ ⟩) ⊢V⦂ Unit
  ex-var-barrier = var (Tl-⟨⟩ Hd) (et-ok Unitₑ)

  ex-var-barrier-ground : ([] ∷ Unit) ⟨ ⊤ᵣ ⟩ ⊢V⦂ Unit
  ex-var-barrier-ground = groundV θ₀ ∅ᴴ-⊨ ex-var-barrier

  -- A variable used after time-passage, and an unboxing: the grades of the
  -- grounded derivations are the interpretations of the mirrored ones.

  ex-var-lock : ∅ᴴ ∣ ((∅ᶜ ∷ Unit) ⟨ rconst uᵣ ⟩) ⊢V⦂ Unit
  ex-var-lock = var (Tl-⟨⟩ Hd) (et-ok Unitₑ)

  ex-var-lock-ground : ([] ∷ Unit) ⟨ uᵣ ⟩ ⊢V⦂ Unit
  ex-var-lock-ground = groundV θ₀ ∅ᴴ-⊨ ex-var-lock

  ex-unbox : ∅ᴴ ∣ (∅ᶜ ∷ [ ûᵣ ] Unit) ⊢C⦂ Unit ‼ ûₑ
  ex-unbox = unbox Hd ⊩≾̂ᵣ-refl (<:̂ᵛ-refl Unit) (return ⋆)

  ex-unbox-ground : [] ∷ [ uᵣ ] Unit ⊢C⦂ Unit ‼ uₑ
  ex-unbox-ground = groundC θ₀ ∅ᴴ-⊨ ex-unbox
