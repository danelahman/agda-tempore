------------------------------------------------------------------------
-- The parameter-free handler algebra at a terminal eternal parameter.    --
--                                                                      --
-- The operational soundness proofs handle at runtime contexts `Γ` with  --
-- `Γ ᴱ ≡ []`, so the fold's eternal-parameter object `P = ⟦ Γ ᴱ ⟧` is   --
-- terminal. Pairing the fold with a (necessarily unique) map `t` into    --
-- `P` yields a parameter-free `T`-algebra `Halg` whose algebra laws are  --
-- exactly the fold's, with the trivial parameter carried by terminality  --
-- rather than by `necᵉ`. This module states and proves those laws        --
-- abstractly, so `Preservation` can instantiate them at `P = ⟦ Γ ᴱ ⟧`.   --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.GroundTypes

module DenotationalSemantics.Model.HandlerAlgebra
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S Cat Fut)
       where

open import Data.Nat using (ℕ)

open import Util.Equality

open import DenotationalSemantics.Model.Modality.BoxCoalg
  Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut

open import DenotationalSemantics.Model.Monad

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open Category Cat
open Future Fut
open GroundTypes GTy

infixr 3 _∙_
_∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
_∙_ = ≈ᵐ-trans

-- `map⇒ᵐ idᵐ k` unfolds to the currying of `k ∘ᵐ appᵐ`, and is functorial in
-- its codomain argument (there is no `map⇒ᵐ-∘` in the interface).
map⇒ᵐ≈curry : ∀ {A B C} → (k : B →ᵐ C) → map⇒ᵐ (idᵐ {A}) k ≈ᵐ curryᵐ (k ∘ᵐ appᵐ)
map⇒ᵐ≈curry k = curryᵐ-cong (∘ᵐ-congʳ (∘ᵐ-congʳ mapˣᵐ-idᵐ ∙ ∘ᵐ-identityʳ _))

map⇒ᵐ-∘ : ∀ {A B C D} → (g : C →ᵐ D) → (f : B →ᵐ C)
         → map⇒ᵐ (idᵐ {A}) (g ∘ᵐ f) ≈ᵐ map⇒ᵐ idᵐ g ∘ᵐ map⇒ᵐ idᵐ f
map⇒ᵐ-∘ g f =
    map⇒ᵐ≈curry (g ∘ᵐ f)
  ∙ curryᵐ-cong (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-congʳ (map⇒ᵐ≈curry f) ∙ map⇒ᵐ-curryᵐ g (f ∘ᵐ appᵐ))

module _ (Mon : Monad S Cat Fut GTy) where

  open Monad Mon

  -- A terminal-ish parameter object: any two maps into it (or into a box of
  -- it) agree. This is what `⟦ Γ ᴱ ⟧` is when `Γ ᴱ ≡ []`.
  module _ {P : Obj}
           (bc : BoxCoalg P)
           (t : ∀ {X} → X →ᵐ P)
           (t-uniq : ∀ {X} → (f g : X →ᵐ P) → f ≈ᵐ g)
           (t-box-uniq : ∀ {X ρ} → (f g : X →ᵐ [ ρ ]ᵒ P) → f ≈ᵐ g)
           {A : Obj}
           (h : Handlerᵀ P A)
         where

    -- The parameter-free algebra: fold with the trivial parameter plugged in.
    Halg : ∀ {ε ε'} → Tᵒ (Tᵒ A ε') ε →ᵐ Tᵒ A (ε ·ₑ ε')
    Halg = T-alg-of-handlerᵀ bc h ∘ᵐ ⟨ t , idᵐ ⟩ᵐ

    -- Inserting the terminal parameter into an exponential's codomain is the
    -- costrength of that insertion: since `P` is terminal, the `exp-strᵐ`
    -- picks out the same (unique) `P` as the direct `map⇒ᵐ`. Box-free.
    strcore-boxfree : ∀ {B C}
                    → exp-strᵐ {P} {B} {C} ∘ᵐ ⟨ t , idᵐ ⟩ᵐ ≈ᵐ map⇒ᵐ idᵐ ⟨ t , idᵐ ⟩ᵐ
    strcore-boxfree =
        ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ≈ᵐ-sym (uncurryᵐ-curryᵐ-iso idᵐ) ⟩ᵐ-cong)
      ∙ exp-strᵐ-⟨⟩ t appᵐ
      ∙ curryᵐ-cong (⟨ t-uniq _ _ , ≈ᵐ-refl ⟩ᵐ-cong)
      ∙ curryᵐ-cong (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ curryᵐ-cong (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-congʳ mapˣᵐ-idᵐ ∙ ∘ᵐ-identityʳ _)))

    -- Extensionality for maps into a boxed product (from `[]-monoidal-η`).
    box-×-ext : ∀ {D E X ρ} → (f g : X →ᵐ [ ρ ]ᵒ (D ×ᵐ E))
              → [ ρ ]ᶠ fstᵐ ∘ᵐ f ≈ᵐ [ ρ ]ᶠ fstᵐ ∘ᵐ g
              → [ ρ ]ᶠ sndᵐ ∘ᵐ f ≈ᵐ [ ρ ]ᶠ sndᵐ ∘ᵐ g
              → f ≈ᵐ g
    box-×-ext f g pf ps =
        ≈ᵐ-sym (∘ᵐ-identityˡ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym []-monoidal-η)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
      ∙ ∘ᵐ-congʳ (⟨ pf , ps ⟩ᵐ-cong)
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ []-monoidal-η
      ∙ ∘ᵐ-identityˡ _

    -- Pairing the (boxed) terminal parameter with a boxed value and combining
    -- monoidally is boxing the direct pairing. The `fstᵐ` legs agree by
    -- terminality of `[ ρ ]ᵒ P`; the `sndᵐ` legs are both the value.
    mono-collapse : ∀ {C X ρ} → (u : X →ᵐ [ ρ ]ᵒ C)
                  → []-monoidal {P} {C} {ρ} ∘ᵐ ⟨ BoxCoalg.necᵉ bc ∘ᵐ t , u ⟩ᵐ
                  ≈ᵐ [ ρ ]ᶠ ⟨ t , idᵐ ⟩ᵐ ∘ᵐ u
    mono-collapse u =
      box-×-ext _ _
        ( ( ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ []-monoidal-fstᵐ ∙ ⟨⟩ᵐ-fstᵐ _ _ )
        ∙ t-box-uniq _ _
        ∙ ≈ᵐ-sym ( ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                 ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
                 ∙ ∘ᵐ-congˡ ([]-congᶠ (⟨⟩ᵐ-fstᵐ _ _)) ) )
        ( ( ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ []-monoidal-sndᵐ ∙ ⟨⟩ᵐ-sndᵐ _ _ )
        ∙ ≈ᵐ-sym ( ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                 ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
                 ∙ ∘ᵐ-congˡ ([]-congᶠ (⟨⟩ᵐ-sndᵐ _ _))
                 ∙ ∘ᵐ-congˡ []-idᵐ
                 ∙ ∘ᵐ-identityˡ _ ) )

    -- The operation law of the collapsed algebra: the same shape the (shared)
    -- `seq-op-core` combinator consumes, with the parameter-free clause
    -- `h op _ ∘ᵐ ⟨ t , idᵐ ⟩ᵐ`. Derived from the fold's own operation law by
    -- collapsing the parameter through terminality.
    Halg-op : ∀ {ε ε'} → (op : Op)
            → Halg {op-grade op ·ₑ ε} {ε'} ∘ᵐ opᵀ {ε = ε} op
            ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε'))
               ∘ᵐ (h op (ε ·ₑ ε') ∘ᵐ ⟨ t , idᵐ ⟩ᵐ)
               ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (Halg {ε} {ε'})))
    Halg-op op =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
      ∙ ∘ᵐ-congʳ (⟨ t-uniq _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-opᵀ op bc h)
      ∙ op-bridge op
      where
        -- The one nontrivial part: the fold's op-law RHS, precomposed with the
        -- terminal parameter, equals the collapsed clause applied to the boxed
        -- continuation. The eternal parameter drops out (terminality), and the
        -- recursive fold under the box/exponential becomes `map⇒ᵐ idᵐ Halg`.
        op-bridge : ∀ {ε ε'} → (op : Op)
                  → (ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε'))
                     ∘ᵐ h op (ε ·ₑ ε')
                     ∘ᵐ ⟨ fstᵐ
                        , ⟨ fstᵐ ∘ᵐ sndᵐ
                          ,   [ mapᵉ (op-grade op) ]ᶠ
                                (curryᵐ (T-alg-of-handlerᵀ bc h
                                  ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ
                                     , appᵐ ∘ᵐ ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ))
                            ∘ᵐ []-monoidal
                            ∘ᵐ mapˣᵐ (BoxCoalg.necᵉ bc {mapᵉ (op-grade op)}) idᵐ
                            ∘ᵐ ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ ⟩ᵐ)
                    ∘ᵐ ⟨ t , idᵐ ⟩ᵐ
                  ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε'))
                     ∘ᵐ (h op (ε ·ₑ ε') ∘ᵐ ⟨ t , idᵐ ⟩ᵐ)
                     ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (Halg {ε} {ε'})))
        op-bridge op =
            ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ
              ( ( ∘ᵐ-assoc _ _ _
                ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
                ∙ ∘ᵐ-congʳ (⟨ ⟨⟩ᵐ-fstᵐ _ _
                            , ⟨⟩ᵐ-∘ _ _ _
                              ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
                                    ∙ ∘ᵐ-identityʳ _
                                , box-core ⟩ᵐ-cong ⟩ᵐ-cong) )
              ∙ ≈ᵐ-sym
                  ( ∘ᵐ-assoc _ _ _
                  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
                  ∙ ∘ᵐ-congʳ (⟨ t-uniq _ _
                              , ∘ᵐ-identityˡ _
                                ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong ⟩ᵐ-cong) ) )
          where
            -- The residual box identity. Both `curryᵐ`s rewrite to
            -- `map⇒ᵐ idᵐ (T-alg-of-handlerᵀ bc h)` composed with `exp-strᵐ` (LHS,
            -- `redA`) resp. the identity (RHS, `redB`); the `[]-monoidal` part
            -- collapses (`mono-collapse`) and the box-free `strcore-boxfree`
            -- finishes it, with `map⇒ᵐ-∘` recombining under the box.
            Talg = T-alg-of-handlerᵀ bc h

            pairs : ⟨ BoxCoalg.necᵉ bc ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ
                      ∘ᵐ (⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ∘ᵐ ⟨ t , idᵐ ⟩ᵐ)
                  ≈ᵐ ⟨ BoxCoalg.necᵉ bc ∘ᵐ t , sndᵐ ⟩ᵐ
            pairs =
                ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _
                          ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
                            , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
                                ∙ ∘ᵐ-identityʳ _ ⟩ᵐ-cong)
              ∙ ⟨⟩ᵐ-∘ _ _ _
              ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                , ∘ᵐ-congˡ (∘ᵐ-identityˡ _) ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong

            redA : curryᵐ (Talg ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ
                                  , appᵐ ∘ᵐ ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ)
                 ≈ᵐ map⇒ᵐ idᵐ Talg ∘ᵐ exp-strᵐ
            redA =
              ≈ᵐ-sym
                ( ∘ᵐ-congʳ exp-strᵐ-def
                ∙ map⇒ᵐ-curryᵐ Talg ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ
                ∙ curryᵐ-cong (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                    , uncurryᵐ-cong (≈ᵐ-sym (∘ᵐ-identityˡ _))
                        ∙ uncurryᵐ-nat sndᵐ idᵐ
                        ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong) ⟩ᵐ-cong)))

            redB : curryᵐ ((Talg ∘ᵐ ⟨ t , idᵐ ⟩ᵐ)
                             ∘ᵐ appᵐ ∘ᵐ ⟨ idᵐ ∘ᵐ fstᵐ , idᵐ ∘ᵐ sndᵐ ⟩ᵐ)
                 ≈ᵐ map⇒ᵐ idᵐ (Talg ∘ᵐ ⟨ t , idᵐ ⟩ᵐ)
            redB =
                curryᵐ-cong (∘ᵐ-congʳ
                  (∘ᵐ-congʳ (⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
                             ∙ ≈ᵐ-sym (⟨⟩ᵐ-unique fstᵐ sndᵐ idᵐ
                                         (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _)))
                   ∙ ∘ᵐ-identityʳ _))
              ∙ ≈ᵐ-sym (map⇒ᵐ≈curry (Talg ∘ᵐ ⟨ t , idᵐ ⟩ᵐ))

            box-core =
                ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
              ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ pairs)
              ∙ ∘ᵐ-congˡ ([]-congᶠ redA)
              ∙ ∘ᵐ-congˡ ([]-∘ᵐ _ _)
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (mono-collapse _))
              ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
              ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
              ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ strcore-boxfree))
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
              ∙ ∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym (map⇒ᵐ-∘ _ _)))
              ∙ ∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym redB))
