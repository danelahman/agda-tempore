------------------------------------------------------------------------
-- The interpretation is natural in renamings:                          --
--   ⟦ C-rename r M ⟧ᶜᵗ ≈ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ r ⟧ʳ    (and dually for values). --
--                                                                    --
-- Proved by mutual induction on the term. The `var` case is            --
-- `var-morphism-nat`; the environment-threading formers push `⟦ r ⟧ʳ`    --
-- through the modality structure using `η⊣`/`strᵀ`/box naturality.      --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module DenotationalSemantics.Interpretation.RenamingCoherence
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Product using (_,_; proj₁; proj₂)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types      S
open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.Renamings  S
open import Syntax.RenActions S using (V-rename; C-rename; var-rename; unbox⇒var)

open Category Cat
open Future Fut
open Past Pst
open Adjunction Adj
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ; eternalᵒ-boxCoalg)
open import DenotationalSemantics.Model.Modality.BoxCoalg
       Cat (GradeSystem.RGrade Grades) Fut using (BoxCoalg)

open import DenotationalSemantics.Interpretation.Types S Cat Fut GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE

-- The resource looked up by an `unbox` is stable under renaming: extending
-- the unboxing renaming `w` by `r` reindexes the looked-up variable exactly
-- along `⟦ r ⟧ʳ`. The two grade bounds are witnesses of the same relation,
-- so they are interchangeable by `⟨⟩-≤-irr`.

unbox⇒var-nat : ∀ {Γ Γ' Δ A ρ} → (r : Ren Γ Γ') → (w : Ren (Δ ⟨ ρ ⟩) Γ) → (V : Δ ⊢V⦂ [ ρ ] A)
              → (ε⊣ ∘ᵐ ⟨⟩-≤ (proj₂ (proj₂ (unbox⇒var (r ∘ʳ w) V)))
                    ∘ᵐ var-proj (proj₁ (proj₂ (unbox⇒var (r ∘ʳ w) V))))
                ≈ᵐ (ε⊣ ∘ᵐ ⟨⟩-≤ (proj₂ (proj₂ (unbox⇒var w V)))
                       ∘ᵐ var-proj (proj₁ (proj₂ (unbox⇒var w V))))
                   ∘ᵐ ⟦ r ⟧ʳ
unbox⇒var-nat r w V with grad-typ⇒var V
... | ρy , y , f , refl
  with var-rename w (Tl-⟨⟩ y)
     | var-rename r (proj₂ (proj₂ (var-rename w (Tl-⟨⟩ y))))
     | var-proj-nat r (proj₂ (proj₂ (var-rename w (Tl-⟨⟩ y))))
... | ρ' , p' , z | ρ'' , p'' , z'' | vpn =
  ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr _ (≾ᵣ-trans p'' _))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-trans p'' _))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ vpn))
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))

-- The interpretation of a restricted renaming also commutes with the
-- necessitations `necᵉ` (the box/`Future` mate of `restrict-ren-mor`, which
-- is stated for `extᵉ`). Derived via `necᵉ-mate` and the adjunction. This is
-- the `BoxCoalg`-morphism premise that the fold's parameter-naturality needs.

restrict-ren-necᵉ : ∀ {Γ Γ'} → (r : Ren Γ Γ') → ∀ {ρ}
                  → [ ρ ]ᶠ ⟦ restrict-ren r ⟧ʳ ∘ᵐ Eternalᵒ.necᵉ (⟦ Γ' ⟧ᴱ-Eternalᵒ) {ρ}
                  ≈ᵐ Eternalᵒ.necᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) {ρ} ∘ᵐ ⟦ restrict-ren r ⟧ʳ
restrict-ren-necᵉ {Γ} {Γ'} r {ρ} =
  ≈ᵐ-trans (∘ᵐ-congʳ (Eternalᵒ.necᵉ-mate (⟦ Γ' ⟧ᴱ-Eternalᵒ)))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym (restrict-ren-mor r))))
  (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
            (∘ᵐ-congˡ (≈ᵐ-sym (Eternalᵒ.necᵉ-mate (⟦ Γ ⟧ᴱ-Eternalᵒ)))))))))))

-- Naturality of the (inverse) associator in its first component: both sides
-- are `⟨ ⟨ f ∘ fstᵐ , fstᵐ ∘ sndᵐ ⟩ , sndᵐ ∘ sndᵐ ⟩`.

×ᵐ-assoc⁻¹-natˡ : ∀ {A A' B C} → (f : A →ᵐ A')
               → ×ᵐ-assoc⁻¹ {A'} {B} {C} ∘ᵐ mapˣᵐ f idᵐ
               ≈ᵐ mapˣᵐ (mapˣᵐ f idᵐ) idᵐ ∘ᵐ ×ᵐ-assoc⁻¹ {A} {B} {C}
×ᵐ-assoc⁻¹-natˡ f =
  ≈ᵐ-trans lhs≈canon (≈ᵐ-sym rhs≈canon)
  where
    sndᵐ-mapˣ : sndᵐ ∘ᵐ mapˣᵐ f idᵐ ≈ᵐ sndᵐ
    sndᵐ-mapˣ = ≈ᵐ-trans (⟨⟩ᵐ-sndᵐ _ _) (∘ᵐ-identityˡ _)
    lhs≈canon =
      ≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
        (⟨ ≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
             (⟨ ⟨⟩ᵐ-fstᵐ _ _
              , ≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ sndᵐ-mapˣ) ⟩ᵐ-cong)
         , ≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ sndᵐ-mapˣ) ⟩ᵐ-cong)
    rhs≈canon =
      ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
        (⟨ ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _) (⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
         , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)

mutual

  V-rename-nat : ∀ {Γ Γ' A} → (r : Ren Γ Γ') → (V : Γ ⊢V⦂ A)
               → ⟦ V-rename r V ⟧ᵛᵗ ≈ᵐ ⟦ V ⟧ᵛᵗ ∘ᵐ ⟦ r ⟧ʳ
  V-rename-nat r (var f x) with var-rename r x | var-morphism-nat r f x
  ... | ρ' , ρ'≾ρ , y | vmn = vmn
  V-rename-nat r (const c) =
    ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
  V-rename-nat r ⋆ = ≈ᵐ-sym terminalᵐ-unique
  V-rename-nat r ⦉ V , W ⦊ =
    ≈ᵐ-trans (⟨ V-rename-nat r V , V-rename-nat r W ⟩ᵐ-cong)
             (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  V-rename-nat r (lam M) =
    ≈ᵐ-trans (curryᵐ-cong (C-rename-nat (cong-∷-ren r) M)) (curryᵐ-nat ⟦ r ⟧ʳ ⟦ M ⟧ᶜᵗ)

  C-rename-nat : ∀ {Γ Γ' C} → (r : Ren Γ Γ') → (M : Γ ⊢C⦂ C)
               → ⟦ C-rename r M ⟧ᶜᵗ ≈ᵐ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ r ⟧ʳ
  C-rename-nat r (return V) =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-rename-nat r V)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  C-rename-nat r (M ⨟ N) =
    ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (C-rename-nat (cong-∷-ren (cong-⟨⟩-ren r)) N))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
                (⟨ η⊣-nat ⟦ r ⟧ʳ
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-rename-nat r M) ⟩ᵐ-cong))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))))))))
  C-rename-nat r (V · W) =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ V-rename-nat r V , V-rename-nat r W ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-rename-nat r (match V `in M) =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-rename-nat (cong-∷-ren (cong-∷-ren r)) M))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
                   (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                    , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                      (≈ᵐ-trans (∘ᵐ-congʳ (V-rename-nat r V))
                                (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong)
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (V-rename-nat r V))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _) , ≈ᵐ-refl ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
  C-rename-nat r (absurd V) =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-rename-nat r V)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  C-rename-nat r (perform op V M) =
    ≈ᵐ-trans (∘ᵐ-congʳ
      (⟨ -- parameter: push `⟦ r ⟧ʳ` past the ground-type coercion
         ≈ᵐ-trans (substᶜ-≈ (ty-gty (param op)) (V-rename-nat r V))
                  (≡→≈ᵐ (sym (substᶜ-∘ (ty-gty (param op)) ⟦ V ⟧ᵛᵗ ⟦ r ⟧ʳ)))
       , -- continuation: coercion, then `curryᵐ`/box/adjunction naturality
         ≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                    (≈ᵐ-trans (substᵈ-≈ (ty-gty (arity op))
                                (C-rename-nat (cong-∷-ren (cong-⟨⟩-ren r)) M))
                              (≡→≈ᵐ (sym (substᵈ-∘ (ty-gty (arity op)) ⟦ M ⟧ᶜᵗ
                                           (⟨ mapᵉ (op-grade op) ⟩ᶠ ⟦ r ⟧ʳ))))))))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-nat _ _)))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
         (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat ⟦ r ⟧ʳ))
                   (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-rename-nat r (delay τ M) =
    ≈ᵐ-sym
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat ⟦ r ⟧ʳ))))
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
                (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym (C-rename-nat (cong-⟨⟩-ren r) M))))))))))
  C-rename-nat {Γ} {Γ'} r (handle_`with_`in {A} {B} {ε} {ε'} M H N) =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , seq-nat ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congˡ alg-nat)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (projᴱ-nat r) , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
    where
      f : ⟦ Γ' ᴱ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ
      f = ⟦ restrict-ren r ⟧ʳ
      -- the second component (`seq`) commutes with the renaming, as for `⨟`
      seq-nat : Tᶠ ⟦ C-rename (cong-∷-ren (cong-⟨⟩-ren r)) N ⟧ᶜᵗ ∘ᵐ strᵀ
                  ∘ᵐ ⟨ η⊣ , ⟦ C-rename r M ⟧ᶜᵗ ⟩ᵐ
              ≈ᵐ (Tᶠ ⟦ N ⟧ᶜᵗ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ ⟩ᵐ) ∘ᵐ ⟦ r ⟧ʳ
      seq-nat =
        ≈ᵐ-trans (∘ᵐ-congˡ (T-congᶠ (C-rename-nat (cong-∷-ren (cong-⟨⟩-ren r)) N)))
        (≈ᵐ-trans (∘ᵐ-congˡ (T-∘ᵐ _ _))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ
                    (⟨ η⊣-nat ⟦ r ⟧ʳ
                     , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-rename-nat r M) ⟩ᵐ-cong)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))))
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))))))
      -- the adapter of `⟦_⟧ʰᵗ` commutes the parameter reindexing past itself
      adapt-commute : ∀ {D D' P Q R S} → (g : D →ᵐ D') → (p : Q →ᵐ P) → (a : S →ᵐ R)
                    → mapˣᵐ (mapˣᵐ g idᵐ) idᵐ ∘ᵐ (mapˣᵐ (mapˣᵐ (idᵐ {D}) p) a ∘ᵐ ×ᵐ-assoc⁻¹)
                    ≈ᵐ (mapˣᵐ (mapˣᵐ (idᵐ {D'}) p) a ∘ᵐ ×ᵐ-assoc⁻¹) ∘ᵐ mapˣᵐ g idᵐ
      adapt-commute g p a =
        ≈ᵐ-trans (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ab≈canon))
        (≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                (≈ᵐ-trans (∘ᵐ-congʳ (×ᵐ-assoc⁻¹-natˡ g))
                (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                          (∘ᵐ-congˡ ba≈canon)))))
        where
          ab≈canon = ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
            (mapˣᵐ-cong (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                                  (mapˣᵐ-cong (∘ᵐ-identityʳ _) (∘ᵐ-identityˡ _)))
                        (∘ᵐ-identityˡ _))
          ba≈canon = ≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
            (mapˣᵐ-cong (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                                  (mapˣᵐ-cong (∘ᵐ-identityˡ _) (∘ᵐ-identityʳ _)))
                        (∘ᵐ-identityʳ _))
      -- the renamed handler equals the original reindexed by `f`
      ⟦⟧ʰᵗ-nat : ∀ op ε''
               → ⟦_⟧ʰᵗ {Γ'} (λ op ε'' Γ'' →
                    C-rename (cong-ren (restrict-ren r)) (H op ε'' Γ'')) op ε''
               ≈ᵐ ⟦_⟧ʰᵗ {Γ} H op ε'' ∘ᵐ mapˣᵐ f idᵐ
      ⟦⟧ʰᵗ-nat op ε'' =
        ≈ᵐ-trans (∘ᵐ-congˡ (C-rename-nat (cong-ren (restrict-ren r)) (H op ε'' [])))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (adapt-commute _ _ _))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      alg-nat : T-alg-of-handlerᵀ (eternalᵒ-boxCoalg (⟦ Γ' ⟧ᴱ-Eternalᵒ))
                  (⟦_⟧ʰᵗ {Γ'} (λ op ε'' Γ'' →
                     C-rename (cong-ren (restrict-ren r)) (H op ε'' Γ'')))
              ≈ᵐ T-alg-of-handlerᵀ (eternalᵒ-boxCoalg (⟦ Γ ⟧ᴱ-Eternalᵒ)) (⟦_⟧ʰᵗ {Γ} H)
                  ∘ᵐ mapˣᵐ f idᵐ
      alg-nat =
        ≈ᵐ-trans (T-alg-of-handlerᵀ-cong (eternalᵒ-boxCoalg (⟦ Γ' ⟧ᴱ-Eternalᵒ)) ⟦⟧ʰᵗ-nat)
                 (T-alg-of-handlerᵀ-natᴾ (eternalᵒ-boxCoalg (⟦ Γ ⟧ᴱ-Eternalᵒ))
                    (eternalᵒ-boxCoalg (⟦ Γ' ⟧ᴱ-Eternalᵒ)) f (restrict-ren-necᵉ r)
                    (⟦_⟧ʰᵗ {Γ} H))
  C-rename-nat r (unbox w V M) =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-rename-nat (cong-∷-ren r) M))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _) (unbox⇒var-nat r w V) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
  C-rename-nat r (box V M) =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-rename-nat (cong-∷-ren r) M))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (V-rename-nat (cong-⟨⟩-ren r) V)))
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
                   (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat ⟦ r ⟧ʳ))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ idᵐ ([ _ ]ᶠ ⟦ V ⟧ᵛᵗ ∘ᵐ η⊣) ⟦ r ⟧ʳ)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
  C-rename-nat r (coerce rel M) =
    ≈ᵐ-trans (∘ᵐ-congʳ (C-rename-nat r M)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
