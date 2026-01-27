-- {-# OPTIONS --allow-unsolved-metas #-}

----------------------------
-- Parallel substitutions --
----------------------------

open import Syntax.Grades

module Syntax.Substitutions (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Syntax.Substitutions.Raw (Grades) public

open import Syntax.Contexts (Grades)
open import Syntax.Extensions (Grades)
open import Syntax.Renamings (Grades)

open import Relation.Binary.PropositionalEquality as Eq hiding ( [_] ) 


record Sub (Γ Γ' : Ctx) : Set where
  constructor sub
  field
    ctx-grade-≾ : ctx-grade Γ' ≾ᵣ ctx-grade Γ
    var-sub     : VSub Γ Γ'

open Sub public

-- Identity substitution

id-sub : ∀ {Γ} → Sub Γ Γ
id-sub {Γ} = sub ≾ᵣ-refl id-vsub

-- -- Composition of substitutions and renamings

-- _∘ʳˢ_ : ∀ {Γ Γ' Γ''} → Sub Γ' Γ'' → Ren Γ Γ' → Sub Γ Γ''
-- s ∘ʳˢ r =
--   sub
--     (≾ᵣ-trans (ctx-grade-≾ s) (ctx-grade-≾ r))
--     (var-sub s ᵛ∘ʳˢ r)

_∘ˢʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Sub Γ Γ' → Sub Γ Γ''
_∘ˢʳ_ r s =
  sub
    (≾ᵣ-trans (ctx-grade-≾ r) (ctx-grade-≾ s))
    (r ᵛ∘ˢʳ var-sub s)

_∘ᵉˢ_ : ∀ {Γ Γ' Γ''} → Sub Γ' Γ'' → Ext Γ Γ' → Sub Γ Γ''
_∘ᵉˢ_ su ex =
  sub
    (≾ᵣ-trans (ctx-grade-≾ su) ((ctx-grade-≾ ex)))
    (var-sub su ᵛ∘ᵉˢ var-extension ex )

-- General congruence substitution

cong-sub : ∀ {Γ Γ' Γ''} → Sub Γ Γ' → Sub (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-sub {Γ} {Γ'} {Γ''} s =
  sub
    (≾ᵣ-trans
      (≾ᵣ-reflexive (ctx-grade-++ᶜ Γ' Γ''))
      (≾ᵣ-trans
        (·ᵣ-monoˡ-≾ᵣ (ctx-grade Γ'') (ctx-grade-≾ s))
        (≾ᵣ-reflexive (sym (ctx-grade-++ᶜ Γ Γ'')))))
    (cong-vsub (var-sub s))

ren⇒sub : ∀ {Γ Γ'} → Ren Γ Γ' → Sub Γ Γ'
ren⇒sub re = sub (ctx-grade-≾ re) (ren⇒vsub re)
