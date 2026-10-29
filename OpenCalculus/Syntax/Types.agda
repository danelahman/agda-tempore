------------------------------------------------------------------
-- Open value and computation types                             --
--                                                              --
-- Value and computation types with grade expressions as        --
-- grades, among them the type variables `tvar` and the         --
-- handler types `_⇛_`. The ground types of the operation       --
-- signature embed by `⌜_⌝ᵍ`.                                   --
------------------------------------------------------------------

open import Grades.Base
open import Language.BaseTypes using (module BaseTypes)
open import Language.Spec

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Syntax.Types (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open BaseTypes BTs using (BaseType)
open import Language.GroundTypes Grades BTs using (GType; Base; Unit; Bool; Nat; Empty; _|×|ᵍ_; _|+|ᵍ_; |List|ᵍ; [_]ᵍ_)

open import OpenCalculus.Syntax.Grades S

-- Open value and computation types

mutual

  data OVType (Θ : Scope) : Set where
    tvar  : TyVar Θ → OVType Θ               -- type variable
    Base  : BaseType → OVType Θ              -- base types
    Unit  : OVType Θ                         -- unit type
    Bool  : OVType Θ                         -- boolean type
    Nat   : OVType Θ                         -- natural-number type
    _|×|_ : OVType Θ → OVType Θ → OVType Θ   -- product type
    _|+|_ : OVType Θ → OVType Θ → OVType Θ   -- sum type
    |List| : OVType Θ → OVType Θ             -- list type
    Empty : OVType Θ                         -- empty type
    _⇒_   : OVType Θ → OCType Θ → OVType Θ   -- function type
    _⇛_   : OCType Θ → OCType Θ → OVType Θ   -- handler type
    [_]_  : RExp Θ → OVType Θ → OVType Θ     -- box modality

  data OCType (Θ : Scope) : Set where
    _‼_ : OVType Θ → EExp Θ → OCType Θ

  infix  37 [_]_
  infix  32 _|×|_ _|+|_
  infixr 30 _⇒_ _⇛_
  infix  31 _‼_

-- Embedding ground types into open types

⌜_⌝ᵍ : ∀ {Θ} → GType → OVType Θ
⌜ Base b ⌝ᵍ    = Base b
⌜ Unit ⌝ᵍ      = Unit
⌜ Bool ⌝ᵍ      = Bool
⌜ Nat ⌝ᵍ       = Nat
⌜ Empty ⌝ᵍ     = Empty
⌜ A |×|ᵍ B ⌝ᵍ  = ⌜ A ⌝ᵍ |×| ⌜ B ⌝ᵍ
⌜ A |+|ᵍ B ⌝ᵍ  = ⌜ A ⌝ᵍ |+| ⌜ B ⌝ᵍ
⌜ |List|ᵍ A ⌝ᵍ = |List| ⌜ A ⌝ᵍ
⌜ [ ρ ]ᵍ A ⌝ᵍ  = [ rconst ρ ] ⌜ A ⌝ᵍ

-- Action of the scope extensions on types

mutual

  wkᵗ-v : ∀ {Θ} → OVType Θ → OVType (Θ +ty)
  wkᵗ-v {Θ} (tvar α) = tvar (wkᵗ-tv Θ α)
  wkᵗ-v     (Base b) = Base b
  wkᵗ-v     Unit     = Unit
  wkᵗ-v     Bool     = Bool
  wkᵗ-v     Nat      = Nat
  wkᵗ-v     (A |×| B) = wkᵗ-v A |×| wkᵗ-v B
  wkᵗ-v     (A |+| B) = wkᵗ-v A |+| wkᵗ-v B
  wkᵗ-v     (|List| A) = |List| (wkᵗ-v A)
  wkᵗ-v     Empty    = Empty
  wkᵗ-v     (A ⇒ C)  = wkᵗ-v A ⇒ wkᵗ-c C
  wkᵗ-v     (C ⇛ D)  = wkᵗ-c C ⇛ wkᵗ-c D
  wkᵗ-v     ([ ρ ] A) = [ wkᵗ-r ρ ] wkᵗ-v A

  wkᵗ-c : ∀ {Θ} → OCType Θ → OCType (Θ +ty)
  wkᵗ-c (A ‼ ε) = wkᵗ-v A ‼ wkᵗ-e ε

mutual

  wkʳ-v : ∀ {Θ} → OVType Θ → OVType (Θ +r)
  wkʳ-v {Θ} (tvar α) = tvar (wkʳ-tv Θ α)
  wkʳ-v     (Base b) = Base b
  wkʳ-v     Unit     = Unit
  wkʳ-v     Bool     = Bool
  wkʳ-v     Nat      = Nat
  wkʳ-v     (A |×| B) = wkʳ-v A |×| wkʳ-v B
  wkʳ-v     (A |+| B) = wkʳ-v A |+| wkʳ-v B
  wkʳ-v     (|List| A) = |List| (wkʳ-v A)
  wkʳ-v     Empty    = Empty
  wkʳ-v     (A ⇒ C)  = wkʳ-v A ⇒ wkʳ-c C
  wkʳ-v     (C ⇛ D)  = wkʳ-c C ⇛ wkʳ-c D
  wkʳ-v     ([ ρ ] A) = [ wkʳ-r ρ ] wkʳ-v A

  wkʳ-c : ∀ {Θ} → OCType Θ → OCType (Θ +r)
  wkʳ-c (A ‼ ε) = wkʳ-v A ‼ wkʳ-e ε

mutual

  wkᵉ-v : ∀ {Θ} → OVType Θ → OVType (Θ +e)
  wkᵉ-v {Θ} (tvar α) = tvar (wkᵉ-tv Θ α)
  wkᵉ-v     (Base b) = Base b
  wkᵉ-v     Unit     = Unit
  wkᵉ-v     Bool     = Bool
  wkᵉ-v     Nat      = Nat
  wkᵉ-v     (A |×| B) = wkᵉ-v A |×| wkᵉ-v B
  wkᵉ-v     (A |+| B) = wkᵉ-v A |+| wkᵉ-v B
  wkᵉ-v     (|List| A) = |List| (wkᵉ-v A)
  wkᵉ-v     Empty    = Empty
  wkᵉ-v     (A ⇒ C)  = wkᵉ-v A ⇒ wkᵉ-c C
  wkᵉ-v     (C ⇛ D)  = wkᵉ-c C ⇛ wkᵉ-c D
  wkᵉ-v     ([ ρ ] A) = [ wkᵉ-r ρ ] wkᵉ-v A

  wkᵉ-c : ∀ {Θ} → OCType Θ → OCType (Θ +e)
  wkᵉ-c (A ‼ ε) = wkᵉ-v A ‼ wkᵉ-e ε
