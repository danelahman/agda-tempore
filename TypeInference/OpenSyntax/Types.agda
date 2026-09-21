-------------------------------------------------------------------
-- Open value and computation types                               --
--                                                                --
-- The types of the mirrored language: the types of `Syntax.Types`--
-- with grades replaced by grade expressions and with an extra    --
-- former `tvar` for type variables. Closed types and ground      --
-- types embed via `⌜_⌝ᵛ` and `⌜_⌝ᵍ`.                             --
-------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec

open import TypeInference.Scopes

module TypeInference.OpenSyntax.Types (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S

open import TypeInference.OpenSyntax.Grades S

-- Open value and computation types

mutual

  data OVType (Θ : Scope) : Set where
    tvar  : TyVar Θ → OVType Θ               -- type variable
    Base  : BaseType → OVType Θ              -- base types
    Unit  : OVType Θ                         -- unit type
    Bool  : OVType Θ                         -- boolean type
    _|×|_ : OVType Θ → OVType Θ → OVType Θ   -- product type
    Empty : OVType Θ                         -- empty type
    _⇒_   : OVType Θ → OCType Θ → OVType Θ   -- function type
    [_]_  : RExp Θ → OVType Θ → OVType Θ     -- box modality

  data OCType (Θ : Scope) : Set where
    _‼_ : OVType Θ → EExp Θ → OCType Θ

  infix  37 [_]_
  infix  32 _|×|_
  infixr 30 _⇒_
  infix  31 _‼_

-- Embedding closed types into open types

mutual

  ⌜_⌝ᵛ : ∀ {Θ} → VType → OVType Θ
  ⌜ Base b ⌝ᵛ    = Base b
  ⌜ Unit ⌝ᵛ      = Unit
  ⌜ Bool ⌝ᵛ      = Bool
  ⌜ A |×| B ⌝ᵛ   = ⌜ A ⌝ᵛ |×| ⌜ B ⌝ᵛ
  ⌜ Empty ⌝ᵛ     = Empty
  ⌜ A ⇒ C ⌝ᵛ     = ⌜ A ⌝ᵛ ⇒ ⌜ C ⌝ᶜ
  ⌜ [ ρ ] A ⌝ᵛ   = [ rconst ρ ] ⌜ A ⌝ᵛ

  ⌜_⌝ᶜ : ∀ {Θ} → CType → OCType Θ
  ⌜ A ‼ ε ⌝ᶜ = ⌜ A ⌝ᵛ ‼ econst ε

-- Embedding ground types into open types (mirrors `type-of-gtype`)

⌜_⌝ᵍ : ∀ {Θ} → GType → OVType Θ
⌜ Base b ⌝ᵍ    = Base b
⌜ Unit ⌝ᵍ      = Unit
⌜ Bool ⌝ᵍ      = Bool
⌜ Empty ⌝ᵍ     = Empty
⌜ A |×|ᵍ B ⌝ᵍ  = ⌜ A ⌝ᵍ |×| ⌜ B ⌝ᵍ
⌜ [ ρ ]ᵍ A ⌝ᵍ  = [ rconst ρ ] ⌜ A ⌝ᵍ

-- Action of the scope extensions on types

mutual

  wkᵗ-v : ∀ {Θ} → OVType Θ → OVType (Θ +ty)
  wkᵗ-v {Θ} (tvar α) = tvar (wkᵗ-tv Θ α)
  wkᵗ-v     (Base b) = Base b
  wkᵗ-v     Unit     = Unit
  wkᵗ-v     Bool     = Bool
  wkᵗ-v     (A |×| B) = wkᵗ-v A |×| wkᵗ-v B
  wkᵗ-v     Empty    = Empty
  wkᵗ-v     (A ⇒ C)  = wkᵗ-v A ⇒ wkᵗ-c C
  wkᵗ-v     ([ ρ ] A) = [ wkᵗ-r ρ ] wkᵗ-v A

  wkᵗ-c : ∀ {Θ} → OCType Θ → OCType (Θ +ty)
  wkᵗ-c (A ‼ ε) = wkᵗ-v A ‼ wkᵗ-e ε

mutual

  wkʳ-v : ∀ {Θ} → OVType Θ → OVType (Θ +r)
  wkʳ-v {Θ} (tvar α) = tvar (wkʳ-tv Θ α)
  wkʳ-v     (Base b) = Base b
  wkʳ-v     Unit     = Unit
  wkʳ-v     Bool     = Bool
  wkʳ-v     (A |×| B) = wkʳ-v A |×| wkʳ-v B
  wkʳ-v     Empty    = Empty
  wkʳ-v     (A ⇒ C)  = wkʳ-v A ⇒ wkʳ-c C
  wkʳ-v     ([ ρ ] A) = [ wkʳ-r ρ ] wkʳ-v A

  wkʳ-c : ∀ {Θ} → OCType Θ → OCType (Θ +r)
  wkʳ-c (A ‼ ε) = wkʳ-v A ‼ wkʳ-e ε

mutual

  wkᵉ-v : ∀ {Θ} → OVType Θ → OVType (Θ +e)
  wkᵉ-v {Θ} (tvar α) = tvar (wkᵉ-tv Θ α)
  wkᵉ-v     (Base b) = Base b
  wkᵉ-v     Unit     = Unit
  wkᵉ-v     Bool     = Bool
  wkᵉ-v     (A |×| B) = wkᵉ-v A |×| wkᵉ-v B
  wkᵉ-v     Empty    = Empty
  wkᵉ-v     (A ⇒ C)  = wkᵉ-v A ⇒ wkᵉ-c C
  wkᵉ-v     ([ ρ ] A) = [ wkᵉ-r ρ ] wkᵉ-v A

  wkᵉ-c : ∀ {Θ} → OCType Θ → OCType (Θ +e)
  wkᵉ-c (A ‼ ε) = wkᵉ-v A ‼ wkᵉ-e ε
