-----------------------------------------------------
-- Substitution of well-typed values for variables --
-----------------------------------------------------

open import Data.Empty
open import Data.Product

open import Function using (case_of_)

open import Relation.Nullary

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.RenActions S
open import Syntax.Renamings  S
open import Syntax.Types      S

-- Substituting a value for a variable in context

⟨_,_⟩[_↦_]var : ∀ {Γ A B ρ ρ'}
          → B ∈[ ρ' ] Γ
          → (¬ Eternal B → ρ' ≾ᵣ uᵣ)
          → (x : A ∈[ ρ ] Γ)
          → split-l x ⊢V⦂ A
          -------------------------------
          → split-l x ++ᶜ split-r x ⊢V⦂ B
          
⟨ Hd , _ ⟩[ Hd ↦ W ]var =
  W
⟨ Hd , f ⟩[ Tl-∷ _ ↦ _ ]var =
  var f Hd
⟨ Tl-∷ y , f ⟩[ Hd ↦ _ ]var =
  var f y
⟨ Tl-∷ y , f ⟩[ Tl-∷ x ↦ W ]var =
  V-rename wk-ren ⟨ y , f ⟩[ x ↦ W ]var
⟨_,_⟩[_↦_]var {B = B} (Tl-⟨⟩ y) f (Tl-⟨⟩ x) W with eternal? B
⟨ Tl-⟨⟩ y , f ⟩[ Tl-⟨⟩ x ↦ W ]var | yes p = -- TODO: check this case (if eternal, we can weaken the grade of Γ)
  eternal-val-ext p ⟨ y , (λ z → ≾ᵣ-zero-productˡ (f (λ z₁ → z p))) ⟩[ x ↦ W ]var
⟨ Tl-⟨⟩ y , f ⟩[ Tl-⟨⟩ x ↦ W ]var | no ¬p = 
  V-rename (⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬p)) ∘ʳ ⟨⟩-η⁻¹-ren) ⟨ y , (λ z → ≾ᵣ-zero-productˡ (f z)) ⟩[ x ↦ W ]var

-- Substituting a value for a variable in a *resource* variable, i.e. one of
-- box type, which is what an `unbox` looks up.
--
-- Unlike `⟨_,_⟩[_↦_]var`, a resource variable's grade is *not* bounded by the
-- unit (that is exactly what `unbox` is for), so it cannot be substituted as
-- a value. It does, however, remain a *variable*: the only value of box type
-- is a variable (`grad-typ⇒var`), so substituting one resource variable for
-- another yields a resource variable again, together with a grade bound.
--
-- The recursion mirrors `⟨_,_⟩[_↦_]var` (and hence the recursion of the
-- context splitting itself), so the interpretation's coherence proof follows
-- the same shape.

⟨_⟩[_↦_]rvar : ∀ {Γ A B ρ σ τ}
             → ([ ρ ] B ∈[ σ ] Γ)
             → (x : A ∈[ τ ] Γ)
             → split-l x ⊢V⦂ A
             ----------------------------------------------------------------
             → Σ[ σ' ∈ R ]
                 (([ ρ ] B ∈[ σ' ] (split-l x ++ᶜ split-r x)) × (σ' ≾ᵣ σ))

-- the resource variable *is* the one being substituted: the value put in its
-- place is of box type, hence a variable (and box types are never eternal,
-- so its grade bound is available)
⟨ Hd ⟩[ Hd ↦ W ]rvar with grad-typ⇒var W
... | σ' , v , f , _ = σ' , v , f (λ ())

-- the resource variable is the head, the substitution acts deeper
⟨ Hd ⟩[ Tl-∷ _ ↦ _ ]rvar = _ , Hd , ≾ᵣ-refl

-- the resource variable is deeper, the substitution replaces the head
⟨ Tl-∷ y ⟩[ Hd ↦ _ ]rvar = _ , y , ≾ᵣ-refl

-- both deeper: recurse
⟨ Tl-∷ y ⟩[ Tl-∷ x ↦ W ]rvar with ⟨ y ⟩[ x ↦ W ]rvar
... | σ' , v , p = σ' , Tl-∷ v , p

⟨ Tl-⟨⟩ y ⟩[ Tl-⟨⟩ x ↦ W ]rvar with ⟨ y ⟩[ x ↦ W ]rvar
... | σ' , v , p = σ' ·ᵣ _ , Tl-⟨⟩ v , ·ᵣ-monoˡ-≾ᵣ p

-- Substituting a value for a variable in a well-typed term

mutual

  _[_↦_]v : ∀ {Γ A B ρ}
          → Γ ⊢V⦂ B
          → (x : A ∈[ ρ ] Γ)
          → split-l x ⊢V⦂ A
          -------------------------------
          → split-l x ++ᶜ split-r x ⊢V⦂ B

  var f y     [ x ↦ W ]v = ⟨ y , f ⟩[ x ↦ W ]var
  const c     [ x ↦ W ]v = const c
  ⦉ V₁ , V₂ ⦊  [ x ↦ W ]v = ⦉ V₁ [ x ↦ W ]v , V₂ [ x ↦ W ]v ⦊
  ⋆           [ x ↦ W ]v = ⋆
  lam M       [ x ↦ W ]v = lam (M [ Tl-∷ x ↦ W ]c)

  _[_↦_]c : ∀ {Γ A C ρ}
          → Γ ⊢C⦂ C
          → (x : A ∈[ ρ ] Γ)
          → split-l x ⊢V⦂ A
          -------------------------------
          → split-l x ++ᶜ split-r x ⊢C⦂ C

  return V        [ x ↦ W ]c = return (V [ x ↦ W ]v)
  (M ⨟ N)         [ x ↦ W ]c = (M [ x ↦ W ]c) ⨟ (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  (V₁ · V₂)       [ x ↦ W ]c = (V₁ [ x ↦ W ]v) · (V₂ [ x ↦ W ]v)
  (match V `in N) [ x ↦ W ]c = match V [ x ↦ W ]v `in (N [ Tl-∷ (Tl-∷ x) ↦ W ]c)
  absurd V        [ x ↦ W ]c = absurd (V [ x ↦ W ]v)
  perform op V M  [ x ↦ W ]c = perform op (V [ x ↦ W ]v) (M [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  delay τ M       [ x ↦ W ]c = delay τ (M [ Tl-⟨⟩ x ↦ W ]c)
  -- The handler clauses close over the eternal part `Γ ᴱ` of the ambient
  -- context (and stay parametric in a further extension `Γ'`). If the
  -- substituted variable is not eternal, it does not occur in `Γ ᴱ`, so the
  -- clauses are only retyped (`ᴱ-drop-split`). If it is eternal, its value
  -- restricts to the eternal context (`eternal-val-restrict`) and is
  -- substituted into each clause at the variable's image, located within
  -- `Γ ᴱ ++ᶜ Γ' ∷ …` via `∈-ᴱ-split`/`split-++ʳ`/`split→∈`.
  _[_↦_]c {A = A} (handle_`with_`in {B = B} M H N) x W with eternal? A
  ... | no ¬et =
    handle (M [ x ↦ W ]c)
    `with (λ op ε'' →
             subst
               (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                          ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                        ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
               (ᴱ-drop-split ¬et x)
               (H op ε''))
    `in (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  ... | yes et =
    handle (M [ x ↦ W ]c)
    `with (λ op ε'' →
             let D = [] ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                 s = split-++ʳ (∈-ᴱ-split et x) D
             in subst (_⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                  (trans (cong₂ _++ᶜ_ (split→∈-split-l s) (split→∈-split-r s))
                    (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D))
                           (cong (_++ᶜ D) (sym (ᴱ-++ᶜ (split-l x) (split-r x))))))
                  ((H op ε'') [ split→∈ s
                                 ↦ subst (_⊢V⦂ A) (sym (split→∈-split-l s))
                                      (eternal-val-restrict et W) ]c))
    `in (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  -- For the value-based unboxing we first recover the underlying resource
  -- variable `y` (and grade bound `rel`) being unboxed via `unbox⇒var`. The
  -- substitution takes it to another resource variable (`⟨_⟩[_↦_]rvar`), from
  -- which we rebuild a value-based unboxing via the `unbox-var` smart
  -- constructor. The new grade bound is the substituted variable's bound
  -- composed with the original one.
  _[_↦_]c (unbox w V M) x W with unbox⇒var w V
  ... | _ , y , rel with ⟨ y ⟩[ x ↦ W ]rvar
  ...   | _ , v , p =
    unbox-var v (≾ᵣ-trans p rel) (M [ Tl-∷ x ↦ W ]c)
  box V N      [ x ↦ W ]c = box (V [ Tl-⟨⟩ x ↦ W ]v) (N [ Tl-∷ x ↦ W ]c)
  coerce rel M [ x ↦ W ]c = coerce rel (M [ x ↦ W ]c)
