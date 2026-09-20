------------------------------------------------------------------------
-- Denotational soundness of the equational theory.                      --
-- Every derivable `M == N` denotes `⟦M⟧ ≈ᵐ ⟦N⟧`.                        --
-- Congruences recurse on their premises; axioms dispatch to their       --
-- own `sound-*` lemma. `Midᵛ`/`Midᶜ` thread certificates the endpoints  --
-- do not determine.                                                     --
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

module EquationalTheory.Soundness
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S using (V-rename; C-rename)
open import Syntax.Substitutions S

open import EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-congᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-congᶠ)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
       using (V-subst-nat; C-subst-nat; subᵛ; subᶜ; substᴾᵛ; substᴾᶜ′;
              subst-ctx-interp; subst-val-interp; sub-env)
open import OperationalSemantics.Soundness.Preservation.Unbox S Cat Fut Pst Adj GTy Mon GE
       using (unbox-def)

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Parametric S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Values S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Modal S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Coerce S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Seq S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.SeqAssoc S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Delay S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.UnboxBeta S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Comm S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Handle S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.HandlePerform S Cat Fut Pst Adj GTy Mon GE

mutual

  {-# TERMINATING #-}

  soundᵛ : ∀ {Γ A} {V W : Γ ⊢V⦂ A} → (p : Γ ⊢V⦂ V == W) → Midᵛ p → Soundᵛ== p
  -- setoid structure
  soundᵛ (V-refl {V = V})     _            pV pW = ⟦⟧ᵛᵗ-irr V pV pW
  soundᵛ (V-sym p)            mp           pV pW = ≈ᵐ-sym (soundᵛ p mp pW pV)
  soundᵛ (V-trans p q)        (pW , mp , mq) pV pU =
    soundᵛ p mp pV pW ∙ soundᵛ q mq pW pU
  -- substitutivity
  soundᵛ (V-subst {V = V} {W = W} p x q U) (pV , pW , pU , mp) pVL pWR =
      ⟦⟧ᵛᵗ-irr (subst (_⊢V⦂ _) q (V [ x ↦ U ]v)) pVL
              (substᴾᵛ {e = q} (V [ x ↦ U ]v) (subᵛ V x U pV pU))
    ∙ subst-val-interp q (V [ x ↦ U ]v) (subᵛ V x U pV pU)
    ∙ ∘ᵐ-congˡ (  V-subst-nat V x U pV pU
                ∙ ∘ᵐ-congˡ (soundᵛ p mp pV pW)
                ∙ ≈ᵐ-sym (V-subst-nat W x U pW pU))
    ∙ ≈ᵐ-sym (subst-val-interp q (W [ x ↦ U ]v) (subᵛ W x U pW pU))
    ∙ ≈ᵐ-sym (⟦⟧ᵛᵗ-irr (subst (_⊢V⦂ _) q (W [ x ↦ U ]v)) pWR
                        (substᴾᵛ {e = q} (W [ x ↦ U ]v) (subᵛ W x U pW pU)))
  -- congruences
  soundᵛ (⦉⦊-cong p q)        (mp , mq)    (pV , pW) (pV' , pW') =
    ⟨ soundᵛ p mp pV pV' , soundᵛ q mq pW pW' ⟩ᵐ-cong
  soundᵛ (lam-cong p)         mp           pM pM' = curryᵐ-cong (soundᶜ p mp pM pM')
  soundᵛ (subV-cong {w = w} {w' = w'} p) mp pV pW =
    ∘ᵐ-cong (⟦⟧<:ᵛ-irr w w') (soundᵛ p mp pV pW)
  -- eta
  soundᵛ (unit-eta V)         _            pV pW = sound-unit-eta V pV pW
  soundᵛ (fun-eta V)          _            pV pW = sound-fun-eta V pV pW
  -- axioms — subsumption
  soundᵛ (subV-refl w V)      _            = sound-subV-refl w V
  soundᵛ (subV-trans w w' w'' V) _         = sound-subV-trans w w' w'' V
  soundᵛ (subV-pair p q V W)  _            = sound-subV-pair p q V W
  soundᵛ (subV-lam p w M)     _            = sound-subV-lam p w M

  soundᶜ : ∀ {Γ C} {M N : Γ ⊢C⦂ C} → (p : Γ ⊢C⦂ M == N) → Midᶜ p → Soundᶜ== p
  -- setoid structure
  soundᶜ (C-refl {M = M})     _            pM pN = ⟦⟧ᶜᵗ-irr M pM pN
  soundᶜ (C-sym p)            mp           pM pN = ≈ᵐ-sym (soundᶜ p mp pN pM)
  soundᶜ (C-trans p q)        (pN , mp , mq) pM pU =
    soundᶜ p mp pM pN ∙ soundᶜ q mq pN pU
  -- substitutivity
  soundᶜ (C-subst {M = M} {N = N} p x q V) (pM , pN , pV , mp) pML pNR =
      ⟦⟧ᶜᵗ-irr (subst (_⊢C⦂ _) q (M [ x ↦ V ]c)) pML
              (substᴾᶜ′ {e = q} (M [ x ↦ V ]c) (subᶜ M x V pM pV))
    ∙ subst-ctx-interp q (M [ x ↦ V ]c) (subᶜ M x V pM pV)
    ∙ ∘ᵐ-congˡ (  C-subst-nat M x V pM pV
                ∙ ∘ᵐ-congˡ (soundᶜ p mp pM pN)
                ∙ ≈ᵐ-sym (C-subst-nat N x V pN pV))
    ∙ ≈ᵐ-sym (subst-ctx-interp q (N [ x ↦ V ]c) (subᶜ N x V pN pV))
    ∙ ≈ᵐ-sym (⟦⟧ᶜᵗ-irr (subst (_⊢C⦂ _) q (N [ x ↦ V ]c)) pNR
                        (substᴾᶜ′ {e = q} (N [ x ↦ V ]c) (subᶜ N x V pN pV)))
  -- congruences
  soundᶜ (return-cong p)      mp           pV pV' = ∘ᵐ-congʳ (soundᵛ p mp pV pV')
  soundᶜ (seq-cong p q)       (mp , mq)    (pM , pN) (pM' , pN') =
    ∘ᵐ-congʳ (∘ᵐ-cong (T-congᶠ (soundᶜ q mq pN pN'))
                      (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , soundᶜ p mp pM pM' ⟩ᵐ-cong)))
  soundᶜ (app-cong p q)       (mp , mq)    (pV , pW) (pV' , pW') =
    ∘ᵐ-congʳ (⟨ soundᵛ p mp pV pV' , soundᵛ q mq pW pW' ⟩ᵐ-cong)
  soundᶜ (match-cong p q)     (mp , mq)    (pV , pM) (pV' , pM') =
    ∘ᵐ-cong (soundᶜ q mq pM pM')
            (⟨ ⟨ ≈ᵐ-refl , ∘ᵐ-congʳ (soundᵛ p mp pV pV') ⟩ᵐ-cong
             , ∘ᵐ-congʳ (soundᵛ p mp pV pV') ⟩ᵐ-cong)
  soundᶜ (absurd-cong p)      mp           pV pV' = ∘ᵐ-congʳ (soundᵛ p mp pV pV')
  soundᶜ (if-cong p q r)      (mp , mq , mr)
         (pV , pM , pN) (pV' , pM' , pN') =
    ifᵐ-cong (soundᵛ p mp pV pV') (soundᶜ q mq pM pM') (soundᶜ r mr pN pN')
  soundᶜ (perform-cong p q)   (mp , mq)    (pV , pM) (pV' , pM') =
    ∘ᵐ-congʳ (⟨ substᶜ-≈ (ty-gty (param _)) (soundᵛ p mp pV pV')
              , ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                  (substᵈ-≈ (ty-gty (arity _)) (soundᶜ q mq pM pM')))) ⟩ᵐ-cong)
  soundᶜ (delay-cong p)       mp           pM pM' =
    ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (soundᶜ p mp pM pM')))
  soundᶜ (handle-cong {H = H} {H' = H'} p hs q) (mp , mhs , mq)
         (pM , pN , pH , uH) (pM' , pN' , pH' , uH') =
    ∘ᵐ-cong (T-alg-of-handlerᵀ-cong _
              (λ op ε'' → ∘ᵐ-congˡ
                            (soundᶜ (hs op ε'') (mhs op ε'')
                                    (pH op ε'') (pH' op ε''))))
            (⟨ ≈ᵐ-refl
             , ∘ᵐ-cong (T-congᶠ (soundᶜ q mq pN pN'))
                       (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , soundᶜ p mp pM pM' ⟩ᵐ-cong)) ⟩ᵐ-cong)
  -- The two nodes name the same variable and differ only in an irrelevant
  -- bound (`unbox-cell-≈`); only the body needs the recursive call.
  soundᶜ (unbox-cong {x = x} {rel = rel} {rel' = rel'} {w = w} {w' = w'}
                     {M = M} {N = N} q)
         mq pM pM' =
      unbox-cell-≈ x x rel rel' w w' refl M pM
    ∙ unbox-def x rel' w' M pM
    ∙ ∘ᵐ-congˡ (soundᶜ q mq pM pM')
    ∙ ≈ᵐ-sym (unbox-def x rel' w' N pM')
  soundᶜ (box-cong p q)       (mp , mq)    (pV , pM) (pV' , pM') =
    ∘ᵐ-cong (soundᶜ q mq pM pM')
            (⟨ ≈ᵐ-refl , ∘ᵐ-congˡ ([]-congᶠ (soundᵛ p mp pV pV')) ⟩ᵐ-cong)
  soundᶜ (subC-cong {w = w} {w' = w'} p) mp pM pN =
    ∘ᵐ-cong (⟦⟧<:ᶜ-irr w w') (soundᶜ p mp pM pN)
  -- axioms — sequencing
  soundᶜ (seq-return V M)     _  = sound-seq-return V M
  soundᶜ (seq-perform V M N)  _  = sound-seq-perform V M N
  soundᶜ (seq-delay M N)      _  = sound-seq-delay M N
  soundᶜ (seq-box V M N)      _  = sound-seq-box V M N
  soundᶜ (seq-unbox x rel w M N) _ = sound-seq-unbox x rel w M N
  soundᶜ (seq-eta M)          _  = sound-seq-eta M
  soundᶜ (seq-assoc M N P)    _  = sound-seq-assoc M N P
  -- axioms — beta/eta
  soundᶜ (fun-beta M W)       _  = sound-fun-beta M W
  soundᶜ (match-beta V W M)   _  = sound-match-beta V W M
  soundᶜ (match-eta V M)      m  = sound-match-eta V M m
  soundᶜ (absurd-eta V M)     _  = sound-absurd-eta V M
  soundᶜ (if-beta-true M N)   _  = sound-if-beta-true M N
  soundᶜ (if-beta-false M N)  _  = sound-if-beta-false M N
  soundᶜ (if-eta V M)         m  = sound-if-eta V M m
  -- axioms — handling
  soundᶜ (handle-return V H N)   _ = sound-handle-return V H N
  soundᶜ (handle-perform V M H N) _ = sound-handle-perform V M H N
  soundᶜ (handle-delay M H N)    _ = sound-handle-delay M H N
  soundᶜ (handle-box V M H N)    _ = sound-handle-box V M H N
  soundᶜ (handle-unbox x rel w M H N) _ = sound-handle-unbox x rel w M H N
  -- axioms — modal
  soundᶜ (unbox-beta V K p w N)  m = sound-unbox-beta V K p w N (proj₁ m) (proj₂ m)
  soundᶜ (unbox-comm x₁ rel₁ w₁ x₂ rel₂ w₂ M) _ =
    sound-unbox-comm x₁ rel₁ w₁ x₂ rel₂ w₂ M
  soundᶜ (box-comm V W M)        _ = sound-box-comm V W M
  soundᶜ (box-unbox-comm V x₂ rel₂ w₂ M) _ = sound-box-unbox-comm V x₂ rel₂ w₂ M
  soundᶜ (boxed-not-used V M)    _ = sound-boxed-not-used V M
  soundᶜ (unbox-not-used x rel w M) _ = sound-unbox-not-used x rel w M
  -- axioms — subsumption
  soundᶜ (subC-refl w M)         _ = sound-subC-refl w M
  soundᶜ (subC-trans w w' w'' M) _ = sound-subC-trans w w' w'' M
  soundᶜ (subC-perform w rel V M) _ = sound-subC-perform w rel V M
  soundᶜ (subC-delay w rel M)    _ = sound-subC-delay w rel M
  soundᶜ (subC-seq w rel M N)    _ = sound-subC-seq w rel M N
  soundᶜ (subC-handle w rel M H N) _ = sound-subC-handle w rel M H N
  soundᶜ (subC-box w V M)        _ = sound-subC-box w V M
  soundᶜ (subC-unbox x rel v w M) _ = sound-subC-unbox x rel v w M
  soundᶜ (subC-handle-in rel M H N) _ = sound-subC-handle-in rel M H N
  -- axioms — delay
  soundᶜ (delay-zero M)          _ = sound-delay-zero M
  soundᶜ (delay-delay M)         m = sound-delay-delay M m
