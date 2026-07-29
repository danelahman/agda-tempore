------------------------------------------------------------------------
-- The coherence theorem itself.
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
module DenotationalSemantics.Interpretation.SubstitutionCoherence.Core
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S
open import Syntax.Substitutions S
open import Syntax.Renamings.Equivalence S using (eternal?-no; unbox-var-ren)

open Category Cat
open Future Fut
open Past Pst
open Adjunction Adj
open GroundTypes GTy
open GroundEternal GE
open Monad Mon

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Base S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Unbox S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Transport S Cat Fut Pst Adj GTy Mon GE

mutual

  subᵛ : ∀ {Γ A B ρ} → (V : Γ ⊢V⦂ B) → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
       → Paramᵛ V → Paramᵛ W → Paramᵛ (V [ x ↦ W ]v)
  subᵛ (var f y)   x W _         pW = subvarᴾ y f x W pW
  subᵛ (const c)   x W _         pW = tt
  subᵛ ⋆           x W _         pW = tt
  subᵛ ⦉ V₁ , V₂ ⦊ x W (p₁ , p₂) pW = subᵛ V₁ x W p₁ pW , subᵛ V₂ x W p₂ pW
  subᵛ (lam M)     x W pM        pW = subᶜ M (Tl-∷ x) W pM pW

  subᶜ : ∀ {Γ A C ρ} → (M : Γ ⊢C⦂ C) → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
       → Paramᶜ M → Paramᵛ W → Paramᶜ (M [ x ↦ W ]c)
  subᶜ (return V)       x W pV        pW = subᵛ V x W pV pW
  subᶜ (M ⨟ N)          x W (pM , pN) pW =
    subᶜ M x W pM pW , subᶜ N (Tl-∷ (Tl-⟨⟩ x)) W pN pW
  subᶜ (V₁ · V₂)        x W (p₁ , p₂) pW = subᵛ V₁ x W p₁ pW , subᵛ V₂ x W p₂ pW
  subᶜ (match V `in N)  x W (pV , pN) pW =
    subᵛ V x W pV pW , subᶜ N (Tl-∷ (Tl-∷ x)) W pN pW
  subᶜ (absurd V)       x W pV        pW = subᵛ V x W pV pW
  subᶜ (perform op V M) x W (pV , pM) pW =
    subᵛ V x W pV pW , subᶜ M (Tl-∷ (Tl-⟨⟩ x)) W pM pW
  subᶜ (delay τ M)      x W pM        pW = subᶜ M (Tl-⟨⟩ x) W pM pW
  subᶜ (unbox w V M)    x W (pV , pM) pW = tt , subᶜ M (Tl-∷ x) W pM pW
  subᶜ (box V N)        x W (pV , pN) pW =
    subᵛ V (Tl-⟨⟩ x) W pV pW , subᶜ N (Tl-∷ x) W pN pW
  subᶜ (coerce rel M)   x W pM        pW = subᶜ M x W pM pW
  subᶜ {Γ = Γ} {A = A} (handle_`with_`in {B = B} M H N) x W (pM , pN , pH , uH) pW
    with eternal? A
  ... | no ¬et =
      subᶜ M x W pM pW
    , subᶜ N (Tl-∷ (Tl-⟨⟩ x)) W pN pW
    , (λ op ε'' → substᴾᶜ (ᴱ-drop-split ¬et x) (H op ε'') (pH op ε''))
    , subst-clauses-uniform (ᴱ-drop-split ¬et x) H pH uH
  ... | yes et =
      subᶜ M x W pM pW
    , subᶜ N (Tl-∷ (Tl-⟨⟩ x)) W pN pW
    -- The clause retyping is spelled out exactly as in `_[_↦_]c`, so that
    -- `substᴾᶜ′`'s equality is solved rather than left to inversion.
    , (λ op ε'' →
         let D = [] ∷ type-of-gtype (param op)
                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
             s = split-++ʳ (∈-ᴱ-split et x) D
             Wv = subst (_⊢V⦂ A) (sym (split→∈-split-l s)) (eternal-val-restrict et W)
             e = trans (cong₂ _++ᶜ_ (split→∈-split-l s) (split→∈-split-r s))
                   (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D))
                          (cong (_++ᶜ D) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
         in substᴾᶜ′ {e = e} ((H op ε'') [ split→∈ s ↦ Wv ]c)
              (subᶜ (H op ε'') (split→∈ s) Wv (pH op ε'')
                 (substᴾᵛ {e = sym (split→∈-split-l s)}
                    (eternal-val-restrict et W) (eternal-val-restrictᴾ et W))))
    , (λ op {ε₁''} {ε₂''} q →
         let D₁ = [] ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₁'')
             D₂ = [] ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε₂'')
             s₁ = split-++ʳ (∈-ᴱ-split et x) D₁
             s₂ = split-++ʳ (∈-ᴱ-split et x) D₂
             Wv₁ = subst (_⊢V⦂ A) (sym (split→∈-split-l s₁)) (eternal-val-restrict et W)
             Wv₂ = subst (_⊢V⦂ A) (sym (split→∈-split-l s₂)) (eternal-val-restrict et W)
             pWv₁ = substᴾᵛ {e = sym (split→∈-split-l s₁)}
                      (eternal-val-restrict et W) (eternal-val-restrictᴾ et W)
             pWv₂ = substᴾᵛ {e = sym (split→∈-split-l s₂)}
                      (eternal-val-restrict et W) (eternal-val-restrictᴾ et W)
             e₁ = trans (cong₂ _++ᶜ_ (split→∈-split-l s₁) (split→∈-split-r s₁))
                    (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D₁))
                           (cong (_++ᶜ D₁) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
             e₂ = trans (cong₂ _++ᶜ_ (split→∈-split-l s₂) (split→∈-split-r s₂))
                    (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D₂))
                           (cong (_++ᶜ D₂) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
         in
          ≈ᵐ-trans (∘ᵐ-congˡ (subst-ctx-interp e₂ ((H op ε₂'') [ split→∈ s₂ ↦ Wv₂ ]c)
                                (subᶜ (H op ε₂'') (split→∈ s₂) Wv₂ (pH op ε₂'') pWv₂)))
          (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (C-subst-nat (H op ε₂'') (split→∈ s₂) Wv₂ (pH op ε₂'') pWv₂)))
          (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))
          (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
          (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-congˡ (eq-ren-∷∷ e₂)) (≈ᵐ-trans (mapˣ-swapᵐ _ _) (∘ᵐ-congʳ (≈ᵐ-trans (mapˣᵐ-cong (mapˣᵐ-cong (eq-ren-irr (ctx-∷-inj (ctx-∷-inj e₂)) (ctx-∷-inj (ctx-∷-inj e₁))) ≈ᵐ-refl) ≈ᵐ-refl) (≈ᵐ-sym (eq-ren-∷∷ e₁))))))) (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (≈ᵐ-trans (∘ᵐ-congˡ (mapˣ-swapᵐ _ _)) (∘ᵐ-assoc _ _ _))))))
          (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
          (≈ᵐ-trans (∘ᵐ-congˡ (uH op q))
          (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
          ((∘ᵐ-congʳ (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (C-subst-nat (H op ε₁'') (split→∈ s₁) Wv₁ (pH op ε₁'') pWv₁))) (≈ᵐ-sym (subst-ctx-interp e₁ ((H op ε₁'') [ split→∈ s₁ ↦ Wv₁ ]c) (subᶜ (H op ε₁'') (split→∈ s₁) Wv₁ (pH op ε₁'') pWv₁)))))))))))))))

  V-subst-nat : ∀ {Γ A B ρ} → (V : Γ ⊢V⦂ B) → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
              → (pV : Paramᵛ V) → (pW : Paramᵛ W)
              → ⟦ V [ x ↦ W ]v ⟧ᵛᵗ (subᵛ V x W pV pW)
              ≈ᵐ ⟦ V ⟧ᵛᵗ pV ∘ᵐ sub-env x W pW
  V-subst-nat (var f y) x W _ pW = sub-var-nat y f x W pW
  V-subst-nat (const c) x W _ pW =
    ≈ᵐ-sym (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ terminalᵐ-unique))
  V-subst-nat ⋆ x W _ pW = ≈ᵐ-sym terminalᵐ-unique
  V-subst-nat ⦉ V₁ , V₂ ⦊ x W (p₁ , p₂) pW =
    ≈ᵐ-trans (⟨ V-subst-nat V₁ x W p₁ pW , V-subst-nat V₂ x W p₂ pW ⟩ᵐ-cong)
             (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  V-subst-nat (lam M) x W pM pW =
    ≈ᵐ-trans (curryᵐ-cong (C-subst-nat M (Tl-∷ x) W pM pW))
             (curryᵐ-nat (sub-env x W pW) (⟦ M ⟧ᶜᵗ pM))

  C-subst-nat : ∀ {Γ A C ρ} → (M : Γ ⊢C⦂ C) → (x : A ∈[ ρ ] Γ) → (W : split-l x ⊢V⦂ A)
              → (pM : Paramᶜ M) → (pW : Paramᵛ W)
              → ⟦ M [ x ↦ W ]c ⟧ᶜᵗ (subᶜ M x W pM pW)
              ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ sub-env x W pW
  C-subst-nat (return V) x W pV pW =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W pV pW)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  C-subst-nat (M ⨟ N) x W (pM , pN) pW =
    ≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (C-subst-nat N (Tl-∷ (Tl-⟨⟩ x)) W pN pW))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
                (⟨ η⊣-nat (sub-env x W pW)
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-subst-nat M x W pM pW) ⟩ᵐ-cong))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))))))))
  C-subst-nat (V₁ · V₂) x W (p₁ , p₂) pW =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ V-subst-nat V₁ x W p₁ pW , V-subst-nat V₂ x W p₂ pW ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-subst-nat (match V `in N) x W (pV , pN) pW =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-subst-nat N (Tl-∷ (Tl-∷ x)) W pN pW))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ _ _ _ _)
                   (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                    , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                      (≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W pV pW))
                                (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong)
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W pV pW))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _) , ≈ᵐ-refl ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
  C-subst-nat (absurd V) x W pV pW =
    ≈ᵐ-trans (∘ᵐ-congʳ (V-subst-nat V x W pV pW)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  C-subst-nat (perform op V M) x W (pV , pM) pW =
    ≈ᵐ-trans (∘ᵐ-congʳ
      (⟨ ≈ᵐ-trans (substᶜ-≈ (ty-gty (param op)) (V-subst-nat V x W pV pW))
                  (≡→≈ᵐ (sym (substᶜ-∘ (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV) (sub-env x W pW))))
       , ≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                    (≈ᵐ-trans (substᵈ-≈ (ty-gty (arity op))
                                (C-subst-nat M (Tl-∷ (Tl-⟨⟩ x)) W pM pW))
                              (≡→≈ᵐ (sym (substᵈ-∘ (ty-gty (arity op)) (⟦ M ⟧ᶜᵗ pM)
                                           (⟨ mapᵉ (op-grade op) ⟩ᶠ (sub-env x W pW)))))))))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-nat _ _)))
         (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
         (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat (sub-env x W pW)))
                   (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  C-subst-nat (delay τ M) x W pM pW =
    ≈ᵐ-sym
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat (sub-env x W pW)))))
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
                (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym (C-subst-nat M (Tl-⟨⟩ x) W pM pW))))))))))
  -- The handle case mirrors `C-rename-nat`'s: the environment-threading second
  -- component commutes as for `⨟` (`seq-nat`), and the handler algebra is
  -- reindexed by `restrict-sub-env x W` (`alg-nat`, via `T-alg-of-handlerᵀ`'s
  -- congruence and naturality-in-P). The substitution splits on whether the
  -- variable is eternal; the two branches differ only in `⟦H'⟧ʰᵗ-nat`, which
  -- relates the substituted clause to the original reindexed clause — a pure
  -- reindexing transport when non-eternal (`restrict-transport`), and the
  -- restricted value placed at the split point when eternal (`eternal-bridge`).
  C-subst-nat {Γ = Γ} {A = A} (handle_`with_`in {A = Aₘ} {B = Bₘ} {ε} {ε'} M H N) x W
              (pM , pN , pH , uH) pW
    with eternal? A
  ... | no ¬et =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , seq-nat ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congˡ alg-nat)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (projᴱ-subst-nat x W pW) , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
    where
      Γ₀ : Ctx
      Γ₀ = split-l x ++ᶜ split-r x
      H' : (op : Op) → (ε'' : E)
         → Γ₀ ᴱ ∷ type-of-gtype (param op)
              ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')
            ⊢C⦂ Bₘ ‼ (op-grade op ·ₑ ε'')
      H' op ε'' =
        subst (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')
                       ⊢C⦂ Bₘ ‼ (op-grade op ·ₑ ε''))
              (ᴱ-drop-split ¬et x) (H op ε'')
      seq-nat : Tᶠ (⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ (subᶜ N (Tl-∷ (Tl-⟨⟩ x)) W pN pW))
                  ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ (subᶜ M x W pM pW) ⟩ᵐ
              ≈ᵐ (Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ) ∘ᵐ sub-env x W pW
      seq-nat =
        ≈ᵐ-trans (∘ᵐ-congˡ (T-congᶠ (C-subst-nat N (Tl-∷ (Tl-⟨⟩ x)) W pN pW)))
        (≈ᵐ-trans (∘ᵐ-congˡ (T-∘ᵐ _ _))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ
                    (⟨ η⊣-nat (sub-env x W pW)
                     , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-subst-nat M x W pM pW) ⟩ᵐ-cong)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))))
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))))))
      pH' : ∀ op ε'' → Paramᶜ (H' op ε'')
      pH' op ε'' = substᴾᶜ (ᴱ-drop-split ¬et x) (H op ε'') (pH op ε'')
      step1 : ∀ op ε''
            → ⟦ H' op ε'' ⟧ᶜᵗ (pH' op ε'')
            ≈ᵐ ⟦ H op ε'' ⟧ᶜᵗ (pH op ε'')
                 ∘ᵐ mapˣᵐ (mapˣᵐ (restrict-sub-env x W) idᵐ) idᵐ
      step1 op ε'' =
        ≈ᵐ-trans (subst-clause-interp (ᴱ-drop-split ¬et x) (H op ε'')
                    (pH op ε''))
                 (∘ᵐ-congʳ ⟦eqren⟧≈)
        where
          ptᵥ = type-of-gtype (param op)
          ktᵥ = [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')
          D₀ = [] ∷ ptᵥ ∷ ktᵥ
          ⟦eqren⟧≈ =
            ≈ᵐ-trans (eq-ren-irr (cong (_++ᶜ D₀) (ᴱ-drop-split ¬et x))
                                 (cong (_∷ ktᵥ) (cong (_∷ ptᵥ) (ᴱ-drop-split ¬et x))))
            (≈ᵐ-trans (eq-ren-∷ (cong (_∷ ptᵥ) (ᴱ-drop-split ¬et x)))
                      (mapˣᵐ-cong
                        (≈ᵐ-trans (eq-ren-∷ (ᴱ-drop-split ¬et x))
                                  (mapˣᵐ-cong
                                    (≈ᵐ-sym (restrict-transport ¬et x W (ᴱ-drop-split ¬et x)))
                                    ≈ᵐ-refl))
                        ≈ᵐ-refl))
      uH' : ∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'')
          → ⟦ H' op ε₂'' ⟧ᶜᵗ (pH' op ε₂'')
              ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
          ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H' op ε₁'' ⟧ᶜᵗ (pH' op ε₁'')
      uH' = subst-clauses-uniform (ᴱ-drop-split ¬et x) H pH uH
      ⟦H'⟧ʰᵗ-nat : ∀ op ε''
                 → clauseᵀ (⟦_⟧ʰᵗ {Γ₀} H' pH' uH') op ε''
                 ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH uH) op ε''
                      ∘ᵐ mapˣᵐ (restrict-sub-env x W) idᵐ
      ⟦H'⟧ʰᵗ-nat op ε'' =
        ≈ᵐ-trans (∘ᵐ-congˡ (step1 op ε''))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (adapt-commute _ _ _))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      alg-nat = T-alg-of-handlerᵀ-natᴾ ((⟦ Γ ⟧ᴱ-Eternalᵒ)) ((⟦ Γ₀ ⟧ᴱ-Eternalᵒ))
                  (restrict-sub-env x W) (restrict-sub-env-necᵉ x W)
                  (⟦_⟧ʰᵗ {Γ} H pH uH) _ ⟦H'⟧ʰᵗ-nat
  ... | yes et =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , seq-nat ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congˡ alg-nat)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨ ≈ᵐ-sym (projᴱ-subst-nat x W pW) , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))
    where
      Γ₀ : Ctx
      Γ₀ = split-l x ++ᶜ split-r x
      H' : (op : Op) → (ε'' : E)
         → Γ₀ ᴱ ∷ type-of-gtype (param op)
              ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')
            ⊢C⦂ Bₘ ‼ (op-grade op ·ₑ ε'')
      H' op ε'' =
        subst (_⊢C⦂ Bₘ ‼ (op-grade op ·ₑ ε''))
          (trans (cong₂ _++ᶜ_ (split→∈-split-l (split-++ʳ (∈-ᴱ-split et x) ([] ∷ type-of-gtype (param op)
                                                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε''))))
                              (split→∈-split-r (split-++ʳ (∈-ᴱ-split et x) ([] ∷ type-of-gtype (param op)
                                                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')))))
            (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) ([] ∷ type-of-gtype (param op)
                                                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε''))))
                   (cong (_++ᶜ ([] ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')))
                         (sym (ᴱ-++ᶜ (split-l x) (split-r x))))))
          ((H op ε'') [ split→∈ (split-++ʳ (∈-ᴱ-split et x) ([] ∷ type-of-gtype (param op)
                                                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')))
                         ↦ subst (_⊢V⦂ A)
                             (sym (split→∈-split-l (split-++ʳ (∈-ᴱ-split et x) ([] ∷ type-of-gtype (param op)
                                                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')))))
                             (eternal-val-restrict et W) ]c)
      seq-nat : Tᶠ (⟦ N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c ⟧ᶜᵗ (subᶜ N (Tl-∷ (Tl-⟨⟩ x)) W pN pW))
                  ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M [ x ↦ W ]c ⟧ᶜᵗ (subᶜ M x W pM pW) ⟩ᵐ
              ≈ᵐ (Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ) ∘ᵐ sub-env x W pW
      seq-nat =
        ≈ᵐ-trans (∘ᵐ-congˡ (T-congᶠ (C-subst-nat N (Tl-∷ (Tl-⟨⟩ x)) W pN pW)))
        (≈ᵐ-trans (∘ᵐ-congˡ (T-∘ᵐ _ _))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ
                    (⟨ η⊣-nat (sub-env x W pW)
                     , ≈ᵐ-trans (∘ᵐ-identityˡ _) (C-subst-nat M x W pM pW) ⟩ᵐ-cong)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))))
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))))))
      pH' : ∀ op ε'' → Paramᶜ (H' op ε'')
      pH' op ε'' =
        let D = [] ∷ type-of-gtype (param op)
                   ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')
            sp = split-++ʳ (∈-ᴱ-split et x) D
            Wv = subst (_⊢V⦂ A) (sym (split→∈-split-l sp)) (eternal-val-restrict et W)
            e = trans (cong₂ _++ᶜ_ (split→∈-split-l sp) (split→∈-split-r sp))
                  (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D))
                         (cong (_++ᶜ D) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
        in substᴾᶜ′ {e = e} ((H op ε'') [ split→∈ sp ↦ Wv ]c)
             (subᶜ (H op ε'') (split→∈ sp) Wv (pH op ε'')
                (substᴾᵛ {e = sym (split→∈-split-l sp)}
                   (eternal-val-restrict et W) (eternal-val-restrictᴾ et W)))
      step1 : ∀ op ε''
            → ⟦ H' op ε'' ⟧ᶜᵗ (pH' op ε'')
            ≈ᵐ ⟦ H op ε'' ⟧ᶜᵗ (pH op ε'')
                 ∘ᵐ mapˣᵐ (mapˣᵐ (restrict-sub-env x W) idᵐ) idᵐ
      step1 op ε'' =
        ≈ᵐ-trans (subst-ctx-interp ctxEq body _)
        (≈ᵐ-trans (∘ᵐ-congˡ (C-subst-nat (H op ε'') (split→∈ s₀) Wᴱ₀
                               (pH op ε'') _))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (∘ᵐ-congʳ
          (≈ᵐ-trans (∘ᵐ-congʳ ⟦ctxEq⟧≈)
          (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                    (mapˣᵐ-cong
                      (≈ᵐ-trans (mapˣᵐ-∘ _ _ _ _)
                                (mapˣᵐ-cong (eternal-bridge-core et x W (canon-e et x)) (∘ᵐ-identityˡ _)))
                      (∘ᵐ-identityˡ _)))))))
        where
          ptᵥ = type-of-gtype (param op)
          ktᵥ = [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε'')
          D₀ = [] ∷ ptᵥ ∷ ktᵥ
          s₀ = split-++ʳ (∈-ᴱ-split et x) D₀
          Wᴱ₀ = subst (_⊢V⦂ A) (sym (split→∈-split-l s₀)) (eternal-val-restrict et W)
          body = (H op ε'') [ split→∈ s₀ ↦ Wᴱ₀ ]c
          ctxEq = trans (cong₂ _++ᶜ_ (split→∈-split-l s₀) (split→∈-split-r s₀))
                    (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D₀))
                           (cong (_++ᶜ D₀) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
          ⟦ctxEq⟧≈ =
            ≈ᵐ-trans (eq-ren-irr ctxEq (cong (_∷ ktᵥ) (cong (_∷ ptᵥ) (canon-e et x))))
            (≈ᵐ-trans (eq-ren-∷ (cong (_∷ ptᵥ) (canon-e et x)))
                      (mapˣᵐ-cong (eq-ren-∷ (canon-e et x)) ≈ᵐ-refl))
      uH' : ∀ (op : Op) {ε₁'' ε₂''} → (q : ε₁'' ≾ₑ ε₂'')
          → ⟦ H' op ε₂'' ⟧ᶜᵗ (pH' op ε₂'')
              ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (T-≤ q)))
          ≈ᵐ T-≤ (·ₑ-monoʳ-≾ₑ q) ∘ᵐ ⟦ H' op ε₁'' ⟧ᶜᵗ (pH' op ε₁'')
      uH' op {ε₁''} {ε₂''} q =
        let D₁ = [] ∷ type-of-gtype (param op)
                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε₁'')
            D₂ = [] ∷ type-of-gtype (param op)
                    ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ Bₘ ‼ ε₂'')
            s₁ = split-++ʳ (∈-ᴱ-split et x) D₁
            s₂ = split-++ʳ (∈-ᴱ-split et x) D₂
            Wv₁ = subst (_⊢V⦂ A) (sym (split→∈-split-l s₁)) (eternal-val-restrict et W)
            Wv₂ = subst (_⊢V⦂ A) (sym (split→∈-split-l s₂)) (eternal-val-restrict et W)
            pWv₁ = substᴾᵛ {e = sym (split→∈-split-l s₁)}
                     (eternal-val-restrict et W) (eternal-val-restrictᴾ et W)
            pWv₂ = substᴾᵛ {e = sym (split→∈-split-l s₂)}
                     (eternal-val-restrict et W) (eternal-val-restrictᴾ et W)
            e₁ = trans (cong₂ _++ᶜ_ (split→∈-split-l s₁) (split→∈-split-r s₁))
                   (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D₁))
                          (cong (_++ᶜ D₁) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
            e₂ = trans (cong₂ _++ᶜ_ (split→∈-split-l s₂) (split→∈-split-r s₂))
                   (trans (sym (++ᶜ-assoc ((split-l x) ᴱ) ((split-r x) ᴱ) D₂))
                          (cong (_++ᶜ D₂) (sym (ᴱ-++ᶜ (split-l x) (split-r x)))))
        in
         ≈ᵐ-trans (∘ᵐ-congˡ (subst-ctx-interp e₂ ((H op ε₂'') [ split→∈ s₂ ↦ Wv₂ ]c)
                               (subᶜ (H op ε₂'') (split→∈ s₂) Wv₂ (pH op ε₂'') pWv₂)))
         (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ (C-subst-nat (H op ε₂'') (split→∈ s₂) Wv₂ (pH op ε₂'') pWv₂)))
         (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-congˡ (eq-ren-∷∷ e₂)) (≈ᵐ-trans (mapˣ-swapᵐ _ _) (∘ᵐ-congʳ (≈ᵐ-trans (mapˣᵐ-cong (mapˣᵐ-cong (eq-ren-irr (ctx-∷-inj (ctx-∷-inj e₂)) (ctx-∷-inj (ctx-∷-inj e₁))) ≈ᵐ-refl) ≈ᵐ-refl) (≈ᵐ-sym (eq-ren-∷∷ e₁))))))) (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (≈ᵐ-trans (∘ᵐ-congˡ (mapˣ-swapᵐ _ _)) (∘ᵐ-assoc _ _ _))))))
         (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
         (≈ᵐ-trans (∘ᵐ-congˡ (uH op q))
         (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
         ((∘ᵐ-congʳ (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (C-subst-nat (H op ε₁'') (split→∈ s₁) Wv₁ (pH op ε₁'') pWv₁))) (≈ᵐ-sym (subst-ctx-interp e₁ ((H op ε₁'') [ split→∈ s₁ ↦ Wv₁ ]c) (subᶜ (H op ε₁'') (split→∈ s₁) Wv₁ (pH op ε₁'') pWv₁))))))))))))))
      ⟦H'⟧ʰᵗ-nat : ∀ op ε''
                 → clauseᵀ (⟦_⟧ʰᵗ {Γ₀} H' pH' uH') op ε''
                 ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH uH) op ε''
                      ∘ᵐ mapˣᵐ (restrict-sub-env x W) idᵐ
      ⟦H'⟧ʰᵗ-nat op ε'' =
        ≈ᵐ-trans (∘ᵐ-congˡ (step1 op ε''))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (adapt-commute _ _ _))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      alg-nat = T-alg-of-handlerᵀ-natᴾ ((⟦ Γ ⟧ᴱ-Eternalᵒ)) ((⟦ Γ₀ ⟧ᴱ-Eternalᵒ))
                  (restrict-sub-env x W) (restrict-sub-env-necᵉ x W)
                  (⟦_⟧ʰᵗ {Γ} H pH uH) _ ⟦H'⟧ʰᵗ-nat
  -- The substitution rebuilds the unboxing with `unbox-var`, so `unbox-var-nat`
  -- turns it back into a lookup; `unbox-step` then splits the goal into the
  -- continuation (the IH) and the lookup (`sub-lk`).
  C-subst-nat (unbox w V M) x W (pV , pM) pW
    with grad-typ⇒var V | var-rename w (Tl-⟨⟩ (proj₁ (proj₂ (grad-typ⇒var V))))
  ... | _ , yv , f , refl | _ , b , y =
    unbox-subst-nat y
      (≾ᵣ-trans (b (λ ())) (≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ (f (λ ()))) (≾ᵣ-reflexive (·ᵣ-identityˡ _))))
      M x W pW (C-subst-nat M (Tl-∷ x) W pM pW)
  C-subst-nat (box V N) x W (pV , pN) pW =
    ≈ᵐ-trans (∘ᵐ-congˡ (C-subst-nat N (Tl-∷ x) W pN pW))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ
                (⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                 , ≈ᵐ-trans (∘ᵐ-identityˡ _)
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (V-subst-nat V (Tl-⟨⟩ x) W pV pW)))
                   (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
                   (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                   (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat (sub-env x W pW)))
                             (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))) ⟩ᵐ-cong))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
  C-subst-nat (coerce rel M) x W pM pW =
    ≈ᵐ-trans (∘ᵐ-congʳ (C-subst-nat M x W pM pW)) (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
