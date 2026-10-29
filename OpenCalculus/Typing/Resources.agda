------------------------------------------------------------------
-- Resource values are annotated variables                      --
--                                                              --
-- A type is a non-resource type if it is neither a type        --
-- variable nor a box type. When every scheme of the program    --
-- context has a non-resource type, a value of box type is a    --
-- resource value: a variable under annotations, reaching a box --
-- type below the value's own (`resource-value`). A value typed --
-- in a context with no variables has a non-resource type       --
-- (`nonResource-closed`).                                      --
--                                                              --
-- A resource value collapses by transitivity to a bound on its --
-- variable's declared type (`res-collapse`), and its           --
-- annotations go over another resource value reaching that     --
-- type (`res-rebase`).                                         --
------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)

open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Typing.Resources (S : LanguageSpec) where

open import OpenCalculus.Syntax.Grades            S
open import OpenCalculus.Syntax.Types             S
open import OpenCalculus.Syntax.Contexts          S
open import OpenCalculus.Syntax.GradeSubstitution S using (Subst; _[_]ᵛ)
open import OpenCalculus.Hypotheses               S
open import OpenCalculus.Typing                   S
open import OpenCalculus.Typing.Erasure           S
open import OpenCalculus.Syntax.Raw               S using (RawV; _⦂ᵛ_)

------------------------------------------------------------------------
-- Non-resource types

NonResource : ∀ {Θ} → OVType Θ → Set
NonResource (tvar α)  = ⊥
NonResource ([ ρ ] A) = ⊥
NonResource _         = ⊤

-- The types of the schemes of a program context

NonResourceDefs : PCtx → Set
NonResourceDefs Δ = ∀ {s k} → s ∈ᵖ[ k ] Δ → NonResource (Xˢ s)

nonResource-∅ : NonResourceDefs ∅ᵖ
nonResource-∅ ()

-- Instances of a non-resource type are non-resource types

nonResource-subst : ∀ {Θ Θ'} → (A : OVType Θ) → (δ : Subst Θ Θ')
                  → NonResource A → NonResource (A [ δ ]ᵛ)
nonResource-subst (Base b)   δ _ = tt
nonResource-subst Unit       δ _ = tt
nonResource-subst Bool       δ _ = tt
nonResource-subst Nat        δ _ = tt
nonResource-subst (A |×| B)  δ _ = tt
nonResource-subst (A |+| B)  δ _ = tt
nonResource-subst (|List| A) δ _ = tt
nonResource-subst Empty      δ _ = tt
nonResource-subst (A ⇒ C)    δ _ = tt
nonResource-subst (C ⇛ D)    δ _ = tt

-- A supertype of a non-resource type is one: subtyping relates type
-- variables only to type variables, and box types only to box types

nonResource-<: : ∀ {Θ} {Q : Hyps Θ} {A B} → Q ∣ A <:̂ᵛ B → NonResource A → NonResource B
nonResource-<: (Baseₛ _)   _ = tt
nonResource-<: Unitₛ       _ = tt
nonResource-<: Boolₛ       _ = tt
nonResource-<: Natₛ        _ = tt
nonResource-<: (_ |×|ₛ _)  _ = tt
nonResource-<: (_ |+|ₛ _)  _ = tt
nonResource-<: (|List|ₛ _) _ = tt
nonResource-<: Emptyₛ      _ = tt
nonResource-<: (_ ⇒ₛ _)    _ = tt
nonResource-<: (_ ⇛ₛ _)    _ = tt

-- A definition's type is an instance of its scheme's

nonResource-usedef : ∀ {Θ} {Δ : PCtx} {s k} {A : OVType Θ}
                   → NonResourceDefs Δ → s ∈ᵖ[ k ] Δ
                   → (δ : Subst (Θˢ s) Θ) → A ≡ Xˢ s [ δ ]ᵛ → NonResource A
nonResource-usedef {s = s} nr f δ refl = nonResource-subst (Xˢ s) δ (nr f)

-- A value in a context with no variables has a non-resource type

nonResource-closed : ∀ {Θ} {Q : Hyps Θ} {Γ : OCtx Θ 0} {A : OVType Θ}
                   → NonResourceDefs (defs Γ) → Q ∣ Γ ⊢V⦂ A → NonResource A
nonResource-closed nr (var x p) with var-pos x
... | ()
nonResource-closed nr (usedef f δ h e) = nonResource-usedef nr f δ e
nonResource-closed nr (const B c)   = tt
nonResource-closed nr ⋆             = tt
nonResource-closed nr true          = tt
nonResource-closed nr false         = tt
nonResource-closed nr zero          = tt
nonResource-closed nr (succ V)      = tt
nonResource-closed nr ⦉ V , W ⦊      = tt
nonResource-closed nr (inl V)       = tt
nonResource-closed nr (inr V)       = tt
nonResource-closed nr nil           = tt
nonResource-closed nr (cons V W)    = tt
nonResource-closed nr (cmp ⋈ V W e) = tt
nonResource-closed nr (lam M)       = tt
nonResource-closed nr (handler N H) = tt
nonResource-closed nr (annᵛ A V)    = nonResource-closed nr V
nonResource-closed nr (subV V p)    = nonResource-<: p (nonResource-closed nr V)

------------------------------------------------------------------------
-- Resource values

-- `V`, of type `[ ρ'' ] X''`, is the variable `z` under annotations,
-- reaching `[ ρ ] X` with `ρ'' ≾ ρ` and `X <: X''`; the variable meets
-- the side condition of `var` at its accumulated grade.

record ResourceValue {Θ n} (Q : Hyps Θ) (Γ : OCtx Θ n) (ρ'' : RExp Θ) (X'' : OVType Θ)
                     (V : RawV Θ n) : Set where
  field
    {res-ρ₀ res-ρ' res-ρ} : RExp Θ
    {res-X₀ res-X}        : OVType Θ
    res-z     : [ res-ρ₀ ] res-X₀ ∈̂[ res-ρ' ] Γ
    usable    : VarOK Q ([ res-ρ₀ ] res-X₀) res-ρ'
    chain     : Q ∣ Γ ⊢↪[ res-ρ' ] res-z ⦂[ res-ρ ] res-X
    erases    : ⌊ chain ⌋ʳ ≡ V
    grade     : Q ⊩ ρ'' ≾̂ᵣ res-ρ
    payload   : Q ∣ res-X <:̂ᵛ X''

open ResourceValue public

-- Lemma (Resource values are annotated variables)

resource-value : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ'' : RExp Θ} {X'' : OVType Θ}
               → NonResourceDefs (defs Γ)
               → (V : Q ∣ Γ ⊢V⦂ [ ρ'' ] X'')
               → ResourceValue Q Γ ρ'' X'' ⌊ V ⌋ᵛ
resource-value nr (var x ok) =
  record { res-z = x ; usable = ok ; chain = res-var ; erases = refl
         ; grade = ⊩≾̂ᵣ-refl ; payload = <:̂ᵛ-refl _ }
resource-value nr (usedef f δ h e) = ⊥-elim (nonResource-usedef nr f δ e)
resource-value {ρ'' = ρ''} {X''} nr (annᵛ _ V) =
  record { res-z = res-z r ; usable = usable r
         ; chain = res-ann ρ'' X'' (chain r) (grade r) (payload r)
         ; erases = cong (_⦂ᵛ [ ρ'' ] X'') (erases r)
         ; grade = ⊩≾̂ᵣ-refl ; payload = <:̂ᵛ-refl _ }
  where r = resource-value nr V
resource-value nr (subV V p) with <:̂ᵛ-boxʳ p
... | _ , _ , refl , q , s =
  record { res-z = res-z r ; usable = usable r ; chain = chain r ; erases = erases r
         ; grade = transᵣ q (grade r) ; payload = <:̂ᵛ-trans (payload r) s }
  where r = resource-value nr V

------------------------------------------------------------------------
-- Collapsing and grafting

-- A resource value's annotations compose to one bound on the variable's
-- declared type

res-collapse : ∀ {Θ n} {Q : Hyps Θ} {Γ : OCtx Θ n} {ρ' ρ₀ ρ : RExp Θ} {X₀ X : OVType Θ}
                 {z : [ ρ₀ ] X₀ ∈̂[ ρ' ] Γ}
             → Q ∣ Γ ⊢↪[ ρ' ] z ⦂[ ρ ] X
             → (Q ⊩ ρ ≾̂ᵣ ρ₀) × (Q ∣ X₀ <:̂ᵛ X)
res-collapse res-var = ⊩≾̂ᵣ-refl , <:̂ᵛ-refl _
res-collapse (res-ann _ _ R p q) with res-collapse R
... | p' , q' = transᵣ p p' , <:̂ᵛ-trans q' q

-- The annotations of a resource value over `z`, of declared type
-- `[ ρ₀ ] X₀`, put over a resource value reaching that type

res-rebase : ∀ {Θ n m} {Q : Hyps Θ} {Γ : OCtx Θ n} {Γ' : OCtx Θ m}
               {ρ' ρ₀ ρ σ' σ₀ : RExp Θ} {X₀ X Y₀ : OVType Θ}
               {z : [ ρ₀ ] X₀ ∈̂[ ρ' ] Γ} {z' : [ σ₀ ] Y₀ ∈̂[ σ' ] Γ'}
           → Q ∣ Γ' ⊢↪[ σ' ] z' ⦂[ ρ₀ ] X₀
           → Q ∣ Γ ⊢↪[ ρ' ] z ⦂[ ρ ] X
           → Q ∣ Γ' ⊢↪[ σ' ] z' ⦂[ ρ ] X
res-rebase R' res-var                 = R'
res-rebase R' (res-ann ρₐ Xₐ R pₐ qₐ) = res-ann ρₐ Xₐ (res-rebase R' R) pₐ qₐ
