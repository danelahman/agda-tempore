------------------------------------------------------------------------
-- The interpretation is natural in renamings:                          --
--   ⟦ C-rename r M ⟧ᶜᵗ ≈ ⟦ M ⟧ᶜᵗ ∘ᵐ ⟦ r ⟧ʳ    (and dually for values). --
--                                                                    --
-- Proved by mutual induction on the term. The `var` case is            --
-- `var-morphism-nat`; the environment-threading formers push `⟦ r ⟧ʳ`    --
-- through the modality structure using `η⊣`/`str`/box naturality.       --
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
  C-rename-nat r (handle M `with H `in N) =
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
