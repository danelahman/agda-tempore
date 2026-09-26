------------------------------------------------------------------------
-- Finite sets of timed traces among the regular ones.                 --
--                                                                     --
-- A non-empty finite set of traces denotes the regular language of    --
-- its runs' encodings. This preserves the unit, products, unions and  --
-- `of-nat`, and it is an order embedding, so the finite sets of       --
-- `Traces.Subsets.RightSided` sit inside the regular grade.           --
--                                                                     --
-- The inclusion does not extend to a morphism of grades: there,       --
-- `any-run` is greatest and absorbing, so a morphism would have to    --
-- make `{ ⟨1⟩ } · ⊤` equal to `⊤`, and here `⊤` holds the empty run   --
-- while `{ ⟨1⟩ } · ⊤` does not (`no-morphism`).                       --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; zero)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)
open import Relation.Binary.PropositionalEquality

module Syntax.Grades.Example.Traces.Regular.Subsets
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (n : ℕ) (code : Op → Fin n)
  (code-injective : ∀ {o o′} → code o ≡ code o′ → o ≡ o′) where

open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; _++_; cartesianProductWith)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ˡ_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product.Base using (_×_; _,_; ∃; ∃₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Nullary using (¬_)

open import Syntax.Grades using (_→ᵍ_)
open import Syntax.Grades.Example.Traces.Regular.Base Op n code code-injective
  using (Word; _∈_; tick; enc; enc-∙; enc-⟨⟩; enc-injective)

import Syntax.Grades.Traces.Sets Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans as S
open S using (Trace; ε; _∙_; NeTraces; neTraces; traces; nf-∈⁺; nf-∈⁻)
import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans as SB
import Syntax.Grades.Example.Traces.Subsets.RightSided Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans as SR
import Syntax.Grades.Example.Traces.Regular.RightSided Op n code code-injective as R
open R using (Regular; table; ⟪_⟫; _·ᴿ_; _⊔ᴿ_; _≾_)

------------------------------------------------------------------------
-- The language of a set of traces

langˡ : Trace → List Trace → Regular
langˡ t []        = ⟪ enc t ⟫
langˡ t (t′ ∷ ts) = ⟪ enc t ⟫ ⊔ᴿ langˡ t′ ts

lang : NeTraces → Regular
lang (neTraces (t ∷ ts)) = langˡ t ts

∈-langˡ⁻ : ∀ t ts w → w ∈ table (langˡ t ts) → ∃ λ s → s ∈ˡ (t ∷ ts) × w ≡ enc s
∈-langˡ⁻ t []        w w∈ = t , here refl , R.∈⟪⟫⁻ (enc t) w w∈
∈-langˡ⁻ t (t′ ∷ ts) w w∈ =
  R.∈⊔-elim ⟪ enc t ⟫ (langˡ t′ ts) (∃ λ s → s ∈ˡ (t ∷ t′ ∷ ts) × w ≡ enc s) w w∈
    (λ w∈t → t , here refl , R.∈⟪⟫⁻ (enc t) w w∈t)
    (λ w∈ts → case ∈-langˡ⁻ t′ ts w w∈ts of λ { (s , s∈ , eq) → s , there s∈ , eq })
  where open import Function.Base using (case_of_)

∈-langˡ⁺ : ∀ t ts {s} → s ∈ˡ (t ∷ ts) → enc s ∈ table (langˡ t ts)
∈-langˡ⁺ t []        (here refl) = R.∈⟪⟫⁺ (enc t)
∈-langˡ⁺ t (t′ ∷ ts) (here refl) = R.∈⊔⁺ˡ ⟪ enc t ⟫ (langˡ t′ ts) (enc t) (R.∈⟪⟫⁺ (enc t))
∈-langˡ⁺ t (t′ ∷ ts) {s} (there s∈) = R.∈⊔⁺ʳ ⟪ enc t ⟫ (langˡ t′ ts) (enc s) (∈-langˡ⁺ t′ ts s∈)

∈-lang⁻ : ∀ P w → w ∈ table (lang P) → ∃ λ s → s ∈ˡ traces P × w ≡ enc s
∈-lang⁻ (neTraces (t ∷ ts)) = ∈-langˡ⁻ t ts

∈-lang⁺ : ∀ P {s} → s ∈ˡ traces P → enc s ∈ table (lang P)
∈-lang⁺ (neTraces (t ∷ ts)) = ∈-langˡ⁺ t ts

------------------------------------------------------------------------
-- An order embedding

lang-mono : ∀ {P Q} → P SR.≾₀ Q → lang P ≾ lang Q
lang-mono {P} {Q} P⊑Q = R.⊆⇒≾ (lang P) (lang Q) λ w w∈ → go w (∈-lang⁻ P w w∈)
  where
  go : ∀ w → (∃ λ s → s ∈ˡ traces P × w ≡ enc s) → w ∈ table (lang Q)
  go w (s , s∈ , eq) =
    subst (λ v → v ∈ table (lang Q)) (sym eq) (∈-lang⁺ Q (SB.∈-⊑ P⊑Q s∈))

lang-reflect : ∀ {P Q} → lang P ≾ lang Q → P SR.≾₀ Q
lang-reflect {P} {Q} le = SB.⊑-∈ λ s s∈ →
  go s (∈-lang⁻ Q (enc s) (R.≾⇒⊆ (lang P) (lang Q) le (enc s) (∈-lang⁺ P s∈)))
  where
  go : ∀ s → (∃ λ s′ → s′ ∈ˡ traces Q × enc s ≡ enc s′) → s ∈ˡ traces Q
  go s (s′ , s′∈ , eq) = subst (_∈ˡ traces Q) (sym (enc-injective eq)) s′∈

------------------------------------------------------------------------
-- Structure preserved

lang-u : lang S.u ≡ R.u
lang-u = cong ⟪_⟫ {x = enc ε} {y = []} refl

lang-of-nat : ∀ m → lang (S.of-nat m) ≡ R.of-nat m
lang-of-nat m = cong ⟪_⟫ (enc-⟨⟩ m)

lang-· : ∀ P Q → lang (P S.· Q) ≡ lang P ·ᴿ lang Q
lang-· P Q = R.same-language (lang (P S.· Q)) (lang P ·ᴿ lang Q) to′ from′
  where
  to′ : ∀ w → w ∈ table (lang (P S.· Q)) → w ∈ table (lang P ·ᴿ lang Q)
  to′ w w∈ with ∈-lang⁻ (P S.· Q) w w∈
  ... | s , s∈ , eq with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q) (nf-∈⁻ s∈)
  ...   | x , y , x∈ , y∈ , refl =
    subst (λ v → v ∈ table (lang P ·ᴿ lang Q)) (sym (trans eq (enc-∙ x y)))
          (R.∈·⁺ (lang P) (lang Q) (enc x) (enc y) (∈-lang⁺ P x∈) (∈-lang⁺ Q y∈))

  from′ : ∀ w → w ∈ table (lang P ·ᴿ lang Q) → w ∈ table (lang (P S.· Q))
  from′ w w∈ = R.∈·-elim (lang P) (lang Q) (λ v → v ∈ table (lang (P S.· Q))) w w∈ λ u v u∈ v∈ →
    go u v (∈-lang⁻ P u u∈) (∈-lang⁻ Q v v∈)
    where
    go : ∀ u v → (∃ λ x → x ∈ˡ traces P × u ≡ enc x) → (∃ λ y → y ∈ˡ traces Q × v ≡ enc y)
       → (u ++ v) ∈ table (lang (P S.· Q))
    go u v (x , x∈ , ex) (y , y∈ , ey) =
      subst (λ z → z ∈ table (lang (P S.· Q)))
            (trans (enc-∙ x y) (sym (cong₂ _++_ ex ey)))
            (∈-lang⁺ (P S.· Q) (nf-∈⁺ (∈-cartesianProductWith⁺ _∙_ x∈ y∈)))

lang-∪ : ∀ P Q → lang (P S.∪ Q) ≡ lang P ⊔ᴿ lang Q
lang-∪ P Q = R.same-language (lang (P S.∪ Q)) (lang P ⊔ᴿ lang Q) to′ from′
  where
  to′ : ∀ w → w ∈ table (lang (P S.∪ Q)) → w ∈ table (lang P ⊔ᴿ lang Q)
  to′ w w∈ with ∈-lang⁻ (P S.∪ Q) w w∈
  ... | s , s∈ , eq with ∈-++⁻ (traces P) (nf-∈⁻ s∈)
  ...   | inj₁ s∈P = subst (λ v → v ∈ table (lang P ⊔ᴿ lang Q)) (sym eq)
                       (R.∈⊔⁺ˡ (lang P) (lang Q) (enc s) (∈-lang⁺ P s∈P))
  ...   | inj₂ s∈Q = subst (λ v → v ∈ table (lang P ⊔ᴿ lang Q)) (sym eq)
                       (R.∈⊔⁺ʳ (lang P) (lang Q) (enc s) (∈-lang⁺ Q s∈Q))

  from′ : ∀ w → w ∈ table (lang P ⊔ᴿ lang Q) → w ∈ table (lang (P S.∪ Q))
  from′ w w∈ = R.∈⊔-elim (lang P) (lang Q) (w ∈ table (lang (P S.∪ Q))) w w∈
    (λ w∈P → case ∈-lang⁻ P w w∈P of λ { (s , s∈ , eq) →
       subst (λ v → v ∈ table (lang (P S.∪ Q))) (sym eq)
             (∈-lang⁺ (P S.∪ Q) (nf-∈⁺ (∈-++⁺ˡ s∈))) })
    (λ w∈Q → case ∈-lang⁻ Q w w∈Q of λ { (s , s∈ , eq) →
       subst (λ v → v ∈ table (lang (P S.∪ Q))) (sym eq)
             (∈-lang⁺ (P S.∪ Q) (nf-∈⁺ (∈-++⁺ʳ (traces P) s∈))) })
    where open import Function.Base using (case_of_)

------------------------------------------------------------------------
-- No morphism of grades

no-morphism : ¬ (SR.right-sided →ᵍ R.right-sided)
no-morphism f = R.∈·-elim (R.of-nat 1) R.⊤ (λ v → v ≡ [] → ⊥) [] []∈ absurd refl
  where
  open _→ᵍ_ f

  -- `{ ⟨1⟩ } · any-run` is `any-run`
  top : R.⊤ ≡ R.of-nat 1 ·ᴿ R.⊤
  top = trans (sym map-⊤)
          (trans (map-· {SR.of-natᵖ 1} {SR.any-run})
                 (cong₂ _·ᴿ_ (map-of-nat {1}) map-⊤))

  []∈ : [] ∈ table (R.of-nat 1 ·ᴿ R.⊤)
  []∈ = subst (λ c → [] ∈ table c) top (R.∈⊤ [])

  absurd : ∀ x y → x ∈ table (R.of-nat 1) → y ∈ table R.⊤ → x ++ y ≡ [] → ⊥
  absurd x y x∈ _ eq with trans (sym (cong (_++ y) (R.∈tick⁻ 1 x x∈))) eq
  ... | ()
