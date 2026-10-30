------------------------------------------------------------------
-- The constraint of a use of a type scheme                     --
--                                                              --
-- `hypsᶜ Q` states the hypotheses `Q` as a constraint, a       --
-- quantified ordering under rigid binders; a substitution      --
-- solves it exactly when the residual hypotheses entail `Q`    --
-- along it (`hypsᶜ-sound`, `hypsᶜ-complete`). `instᶜ s A`      --
-- states that some instance of the scheme `s` has a type below --
-- `A` and its hypotheses entailed (`instᶜ-sound`,              --
-- `instᶜ-complete`).                                           --
------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.Constraints.Schemes (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Syntax.Contexts          S using (Scheme; Θˢ; Qˢ; Xˢ)
open import PolymorphicCalculus.Hypotheses               S

open import PolymorphicCalculus.Inference.Constraints.Syntax       S
open import PolymorphicCalculus.Inference.Constraints.Satisfaction S
open import PolymorphicCalculus.Inference.Constraints.Properties   S

------------------------------------------------------------------------
-- Hypotheses as a constraint

ordsᶜ : ∀ {Θ} → Ords Θ → Constraint Θ
ordsᶜ o = ⋀ᴸ (ors o) (λ { (ρ , ρ') → ρ ≾̂ᵣᶜ ρ' }) ∧̂ ⋀ᴸ (oes o) (λ { (ε , ε') → ε ≾̂ₑᶜ ε' })

hypsᶜ : ∀ {Θ} → Hyps Θ → Constraint Θ
hypsᶜ Q =
  ⋀ᴸ (ets Q) (λ α → Etᶜ (tvar α))
  ∧̂ ⋀ᴸ (subᵥ Q) (λ { (α , β) → tvar α ≾̂ᵥᶜ tvar β })
  ∧̂ ⋀ᴸ (ordᵣ Q) (λ { (ρ , ρ') → ρ ≾̂ᵣᶜ ρ' })
  ∧̂ ⋀ᴸ (ordₑ Q) (λ { (ε , ε') → ε ≾̂ₑᶜ ε' })
  ∧̂ ⋀ᴸ (disj Q) (λ { (A , ρ) → Et∨≾ᵘ A ρ })
  ∧̂ ⋀ᴸ (qhyps Q) (λ O → ∀ᵉⁿ (rigids O) (ordsᶜ (body O)))

-- The use of a scheme: an instance of its variables at which its type
-- is below the expected one and its hypotheses hold

instᶜ-body : ∀ {Θ} → (s : Scheme) → OVType Θ → Constraint (Θ ⊹ Θˢ s)
instᶜ-body s A =
  (Xˢ s [ newˢ⊹ (Θˢ s) ]ᵛ ≾̂ᵥᶜ A [ wkˢ⊹ (Θˢ s) ]ᵛ) ∧̂ hypsᶜ (Qˢ s) [ newˢ⊹ (Θˢ s) ]ᶜⁿ

instᶜ : ∀ {Θ} → Scheme → OVType Θ → Constraint Θ
instᶜ s A = ∃ˢ (Θˢ s) (instᶜ-body s A)

------------------------------------------------------------------------
-- Satisfaction of the derived forms

module _ {Θ Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'} where

  ⋀ᴸ-elim : ∀ {A : Set} {xs : List A} {f : A → Constraint Θ}
          → σ ⊨[ Q ] ⋀ᴸ xs f → ∀ {x} → x ∈ xs → σ ⊨[ Q ] f x
  ⋀ᴸ-elim (h , _) (here refl) = h
  ⋀ᴸ-elim (_ , h) (there m)   = ⋀ᴸ-elim h m

  ⋀ᴸ-intro : ∀ {A : Set} (xs : List A) {f : A → Constraint Θ}
           → (∀ {x} → x ∈ xs → σ ⊨[ Q ] f x) → σ ⊨[ Q ] ⋀ᴸ xs f
  ⋀ᴸ-intro []       h = tt
  ⋀ᴸ-intro (x ∷ xs) h = h (here refl) , ⋀ᴸ-intro xs (λ m → h (there m))

∀ᵉⁿ-elim : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} (k : ℕ) {C : Constraint (Θ +eⁿ k)}
         → σ ⊨[ Q ] ∀ᵉⁿ k C → (σ ↑ᵉⁿ k) ⊨[ wkᵉⁿ-H k Q ] C
∀ᵉⁿ-elim zero    h = h
∀ᵉⁿ-elim (suc k) h = ∀ᵉⁿ-elim k h

∀ᵉⁿ-intro : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} (k : ℕ) {C : Constraint (Θ +eⁿ k)}
          → (σ ↑ᵉⁿ k) ⊨[ wkᵉⁿ-H k Q ] C → σ ⊨[ Q ] ∀ᵉⁿ k C
∀ᵉⁿ-intro zero    h = h
∀ᵉⁿ-intro (suc k) h = ∀ᵉⁿ-intro k h

-- Existentials over the variables of one sort, and of a scope

∃ᵗ*-intro : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} (a : ℕ)
              {C : Constraint (scope (a + nTy Θ) (nR Θ) (nE Θ))}
          → (ts : Fin a → OVType Θ') → (σ ⊕ᵗ ts) ⊨[ Q ] C → σ ⊨[ Q ] ∃ᵗ* a C
∃ᵗ*-intro zero    ts h = h
∃ᵗ*-intro (suc a) ts h = ∃ᵗ*-intro a (λ α → ts (suc α)) (ts zero , h)

∃ᵗ*-elim : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} (a : ℕ)
             {C : Constraint (scope (a + nTy Θ) (nR Θ) (nE Θ))}
         → σ ⊨[ Q ] ∃ᵗ* a C → Σ[ ts ∈ (Fin a → OVType Θ') ] (σ ⊕ᵗ ts) ⊨[ Q ] C
∃ᵗ*-elim zero    h = (λ ()) , h
∃ᵗ*-elim (suc a) h with ∃ᵗ*-elim a h
... | ts , (B , h') = (λ { zero → B ; (suc α) → ts α }) , h'

∃ʳ*-intro : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} (b : ℕ)
              {C : Constraint (scope (nTy Θ) (b + nR Θ) (nE Θ))}
          → (rs : Fin b → RExp Θ') → (σ ⊕ʳ rs) ⊨[ Q ] C → σ ⊨[ Q ] ∃ʳ* b C
∃ʳ*-intro zero    rs h = h
∃ʳ*-intro (suc b) rs h = ∃ʳ*-intro b (λ i → rs (suc i)) (rs zero , h)

∃ʳ*-elim : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} (b : ℕ)
             {C : Constraint (scope (nTy Θ) (b + nR Θ) (nE Θ))}
         → σ ⊨[ Q ] ∃ʳ* b C → Σ[ rs ∈ (Fin b → RExp Θ') ] (σ ⊕ʳ rs) ⊨[ Q ] C
∃ʳ*-elim zero    h = (λ ()) , h
∃ʳ*-elim (suc b) h with ∃ʳ*-elim b h
... | rs , (ρ , h') = (λ { zero → ρ ; (suc i) → rs i }) , h'

∃ᵉ*-intro : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} (c : ℕ)
              {C : Constraint (scope (nTy Θ) (nR Θ) (c + nE Θ))}
          → (es : Fin c → EExp Θ') → (σ ⊕ᵉ es) ⊨[ Q ] C → σ ⊨[ Q ] ∃ᵉ* c C
∃ᵉ*-intro zero    es h = h
∃ᵉ*-intro (suc c) es h = ∃ᵉ*-intro c (λ i → es (suc i)) (es zero , h)

∃ᵉ*-elim : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} (c : ℕ)
             {C : Constraint (scope (nTy Θ) (nR Θ) (c + nE Θ))}
         → σ ⊨[ Q ] ∃ᵉ* c C → Σ[ es ∈ (Fin c → EExp Θ') ] (σ ⊕ᵉ es) ⊨[ Q ] C
∃ᵉ*-elim zero    h = (λ ()) , h
∃ᵉ*-elim (suc c) h with ∃ᵉ*-elim c h
... | es , (ε , h') = (λ { zero → ε ; (suc i) → es i }) , h'

∃ˢ-intro : ∀ {Θ Θ' Ψ} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {C : Constraint (Θ ⊹ Ψ)}
         → (δ : Subst Ψ Θ') → (σ ⊕ˢ δ) ⊨[ Q ] C → σ ⊨[ Q ] ∃ˢ Ψ C
∃ˢ-intro {Ψ = Ψ} δ h =
  ∃ᵗ*-intro (nTy Ψ) (sTy δ) (∃ʳ*-intro (nR Ψ) (sR δ) (∃ᵉ*-intro (nE Ψ) (sE δ) h))

∃ˢ-elim : ∀ {Θ Θ' Ψ} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {C : Constraint (Θ ⊹ Ψ)}
        → σ ⊨[ Q ] ∃ˢ Ψ C → Σ[ δ ∈ Subst Ψ Θ' ] (σ ⊕ˢ δ) ⊨[ Q ] C
∃ˢ-elim {Ψ = Ψ} h with ∃ᵗ*-elim (nTy Ψ) h
... | ts , h₁ with ∃ʳ*-elim (nR Ψ) h₁
... | rs , h₂ with ∃ᵉ*-elim (nE Ψ) h₂
... | es , h₃ = sub ts rs es , h₃

------------------------------------------------------------------------
-- Hypotheses as a constraint are solved by entailment

module _ {Θ Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'} where

  ordsᶜ-sound : (o : Ords Θ) → σ ⊨[ Q ] ordsᶜ o → Q ⊩ᵒ o [ σ ]
  ordsᶜ-sound o (hr , he) = mk⊩ᵒ (⋀ᴸ-elim hr) (⋀ᴸ-elim he)

  ordsᶜ-complete : (o : Ords Θ) → Q ⊩ᵒ o [ σ ] → σ ⊨[ Q ] ordsᶜ o
  ordsᶜ-complete o h = ⋀ᴸ-intro (ors o) (⊩ors h) , ⋀ᴸ-intro (oes o) (⊩oes h)

hypsᶜ-sound : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} (Q' : Hyps Θ)
            → σ ⊨[ Q ] hypsᶜ Q' → Q ⊩ᴴ Q' [ σ ]
hypsᶜ-sound Q' (h₁ , h₂ , h₃ , h₄ , h₅ , h₆) =
  mk⊩ᴴ (⋀ᴸ-elim h₁) (⋀ᴸ-elim h₂) (⋀ᴸ-elim h₃) (⋀ᴸ-elim h₄) (⋀ᴸ-elim h₅)
       (λ {O} m → ordsᶜ-sound (body O) (∀ᵉⁿ-elim (rigids O) (⋀ᴸ-elim h₆ m)))

hypsᶜ-complete : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} (Q' : Hyps Θ)
               → Q ⊩ᴴ Q' [ σ ] → σ ⊨[ Q ] hypsᶜ Q'
hypsᶜ-complete Q' h =
  ⋀ᴸ-intro (ets Q') (⊩ets h) , ⋀ᴸ-intro (subᵥ Q') (⊩subᵥ h) , ⋀ᴸ-intro (ordᵣ Q') (⊩ordᵣ h)
  , ⋀ᴸ-intro (ordₑ Q') (⊩ordₑ h) , ⋀ᴸ-intro (disj Q') (⊩disj h)
  , ⋀ᴸ-intro (qhyps Q') (λ {O} m → ∀ᵉⁿ-intro (rigids O) (ordsᶜ-complete (body O) (⊩qhyps h m)))

------------------------------------------------------------------------
-- The use of a scheme

instᶜ-sound : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} (s : Scheme) (A : OVType Θ)
            → σ ⊨[ Q ] instᶜ s A
            → Σ[ δ ∈ Subst (Θˢ s) Θ' ] (Q ∣ Xˢ s [ δ ]ᵛ <:̂ᵛ A [ σ ]ᵛ) × (Q ⊩ᴴ Qˢ s [ δ ])
instᶜ-sound {σ = σ} {Q} s A h with ∃ˢ-elim {Ψ = Θˢ s} {σ = σ} {Q = Q} {C = instᶜ-body s A} h
... | δ , (st , hq) =
  δ , subst₂ (Q ∣_<:̂ᵛ_) eX eA st ,
  hypsᶜ-sound (Qˢ s)
    (⊨-resp-≐ˢ (newˢ⊹-⊕ˢ σ δ) (hypsᶜ (Qˢ s)) (⊨-subst⁻ (hypsᶜ (Qˢ s)) hq))
  where
    eX : Xˢ s [ newˢ⊹ (Θˢ s) ]ᵛ [ σ ⊕ˢ δ ]ᵛ ≡ Xˢ s [ δ ]ᵛ
    eX = trans ([⨟]ᵛ (Xˢ s) (newˢ⊹ (Θˢ s)) (σ ⊕ˢ δ)) ([≐]ᵛ (newˢ⊹-⊕ˢ σ δ) (Xˢ s))

    eA : A [ wkˢ⊹ (Θˢ s) ]ᵛ [ σ ⊕ˢ δ ]ᵛ ≡ A [ σ ]ᵛ
    eA = trans ([⨟]ᵛ A (wkˢ⊹ (Θˢ s)) (σ ⊕ˢ δ)) ([≐]ᵛ (wkˢ⊹-⊕ˢ σ δ) A)

instᶜ-complete : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'} (s : Scheme) (A : OVType Θ)
               → (δ : Subst (Θˢ s) Θ') → Q ∣ Xˢ s [ δ ]ᵛ <:̂ᵛ A [ σ ]ᵛ → Q ⊩ᴴ Qˢ s [ δ ]
               → σ ⊨[ Q ] instᶜ s A
instᶜ-complete {σ = σ} {Q} s A δ st hq =
  ∃ˢ-intro {Ψ = Θˢ s} {σ = σ} {Q = Q} {C = instᶜ-body s A} δ
    (subst₂ (Q ∣_<:̂ᵛ_) (sym eX) (sym eA) st ,
     ⊨-subst (hypsᶜ (Qˢ s))
       (⊨-resp-≐ˢ (≐ˢ-sym (newˢ⊹-⊕ˢ σ δ)) (hypsᶜ (Qˢ s)) (hypsᶜ-complete (Qˢ s) hq)))
  where
    eX : Xˢ s [ newˢ⊹ (Θˢ s) ]ᵛ [ σ ⊕ˢ δ ]ᵛ ≡ Xˢ s [ δ ]ᵛ
    eX = trans ([⨟]ᵛ (Xˢ s) (newˢ⊹ (Θˢ s)) (σ ⊕ˢ δ)) ([≐]ᵛ (newˢ⊹-⊕ˢ σ δ) (Xˢ s))

    eA : A [ wkˢ⊹ (Θˢ s) ]ᵛ [ σ ⊕ˢ δ ]ᵛ ≡ A [ σ ]ᵛ
    eA = trans ([⨟]ᵛ A (wkˢ⊹ (Θˢ s)) (σ ⊕ˢ δ)) ([≐]ᵛ (wkˢ⊹-⊕ˢ σ δ) A)

------------------------------------------------------------------------
-- Without quantified hypotheses, the constraint has no rigid binder

⋀ᴸ-rigidFree : ∀ {Θ} {A : Set} (xs : List A) {f : A → Constraint Θ}
             → (∀ x → RigidFree (f x)) → RigidFree (⋀ᴸ xs f)
⋀ᴸ-rigidFree []       r = tt
⋀ᴸ-rigidFree (x ∷ xs) r = r x , ⋀ᴸ-rigidFree xs r

∃ᵗ*-rigidFree : ∀ {Θ} (a : ℕ) {C : Constraint (scope (a + nTy Θ) (nR Θ) (nE Θ))}
              → RigidFree C → RigidFree (∃ᵗ* a C)
∃ᵗ*-rigidFree zero    r = r
∃ᵗ*-rigidFree (suc a) r = ∃ᵗ*-rigidFree a r

∃ʳ*-rigidFree : ∀ {Θ} (b : ℕ) {C : Constraint (scope (nTy Θ) (b + nR Θ) (nE Θ))}
              → RigidFree C → RigidFree (∃ʳ* b C)
∃ʳ*-rigidFree zero    r = r
∃ʳ*-rigidFree (suc b) r = ∃ʳ*-rigidFree b r

∃ᵉ*-rigidFree : ∀ {Θ} (c : ℕ) {C : Constraint (scope (nTy Θ) (nR Θ) (c + nE Θ))}
              → RigidFree C → RigidFree (∃ᵉ* c C)
∃ᵉ*-rigidFree zero    r = r
∃ᵉ*-rigidFree (suc c) r = ∃ᵉ*-rigidFree c r

[]ᶜⁿ-rigidFree : ∀ {Θ Θ'} (C : Constraint Θ) (σ : Subst Θ Θ') → RigidFree C → RigidFree (C [ σ ]ᶜⁿ)
[]ᶜⁿ-rigidFree ⊤̂           σ r       = tt
[]ᶜⁿ-rigidFree ⊥̂           σ r       = tt
[]ᶜⁿ-rigidFree (C ∧̂ D)     σ (r , q) = []ᶜⁿ-rigidFree C σ r , []ᶜⁿ-rigidFree D σ q
[]ᶜⁿ-rigidFree (A ≾̂ᵥᶜ B)   σ r       = tt
[]ᶜⁿ-rigidFree (ρ ≾̂ᵣᶜ ρ')  σ r       = tt
[]ᶜⁿ-rigidFree (ε ≾̂ₑᶜ ε')  σ r       = tt
[]ᶜⁿ-rigidFree (Etᶜ A)     σ r       = tt
[]ᶜⁿ-rigidFree (Et∨≾ᵘ A ρ) σ r       = tt
[]ᶜⁿ-rigidFree (∃ᵗ C)      σ r       = []ᶜⁿ-rigidFree C (σ ↑ᵗ) r
[]ᶜⁿ-rigidFree (∃ʳ C)      σ r       = []ᶜⁿ-rigidFree C (σ ↑ʳ) r
[]ᶜⁿ-rigidFree (∃ᵉ C)      σ r       = []ᶜⁿ-rigidFree C (σ ↑ᵉ) r
[]ᶜⁿ-rigidFree (⋀ᵒᵖ f)     σ r       = λ op → []ᶜⁿ-rigidFree (f op) σ (r op)

hypsᶜ-rigidFree : ∀ {Θ} (Q : Hyps Θ) → qhyps Q ≡ [] → RigidFree (hypsᶜ Q)
hypsᶜ-rigidFree (hyps et sb oR oE dj []) refl =
  ⋀ᴸ-rigidFree et (λ _ → tt) , ⋀ᴸ-rigidFree sb (λ _ → tt) , ⋀ᴸ-rigidFree oR (λ _ → tt)
  , ⋀ᴸ-rigidFree oE (λ _ → tt) , ⋀ᴸ-rigidFree dj (λ _ → tt) , tt

instᶜ-rigidFree : ∀ {Θ} (s : Scheme) (A : OVType Θ) → qhyps (Qˢ s) ≡ [] → RigidFree (instᶜ s A)
instᶜ-rigidFree {Θ} s A e =
  ∃ᵗ*-rigidFree (nTy (Θˢ s))
    (∃ʳ*-rigidFree (nR (Θˢ s))
      (∃ᵉ*-rigidFree (nE (Θˢ s))
        (tt , []ᶜⁿ-rigidFree (hypsᶜ (Qˢ s)) (newˢ⊹ (Θˢ s)) (hypsᶜ-rigidFree (Qˢ s) e))))
