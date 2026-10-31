------------------------------------------------------------------------
-- Finite sets of timed traces among the regular ones.                --
--                                                                    --
-- A non-empty finite set of traces denotes the regular language of   --
-- the encodings of its runs. The map preserves the unit, products,   --
-- unions and `of-dur`, and is an order embedding: the finite sets of --
-- `Traces.Subsets.RightSided` embed in the regular grade.            --
--                                                                    --
-- The embedding is not a grade morphism: `any-run` is greatest and   --
-- absorbing in the finite sets, so a morphism would identify         --
-- `{ ⟨1⟩ } · ⊤` with `⊤`, whereas in the regular grade `⊤` contains  --
-- the empty run and `{ ⟨1⟩ } · ⊤` does not (`no-morphism`).          --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Data.Nat.Base using (ℕ; suc)
open import Data.Fin.Base using (Fin; zero)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)
open import Relation.Binary.PropositionalEquality

open import Grades.Durations.Nat using (ℕᵀ)

module Grades.Examples.Traces.Regular.Subsets
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

open import Grades.Base using (_→ᵍ_; Grade)
open import Data.Product.Base using (proj₁; proj₂)
open import Grades.Examples.Traces.Regular.Base Op n code code-injective
  using (Word; _∈_; tick; enc; enc-∙; enc-⟨⟩; enc-injective)

import Grades.Traces.Sets ℕᵀ Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans as S
open S using (Trace; ε; _∙_; NeTraces; neTraces; traces; nf-∈⁺; nf-∈⁻)
import Grades.Examples.Traces.Subsets.Base Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans as SB
import Grades.Examples.Traces.Subsets.RightSided Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans as SR
import Grades.Examples.Traces.Regular.RightSided Op n code code-injective as R
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

lang-of-dur : ∀ m → lang (S.of-dur m) ≡ R.of-dur m
lang-of-dur m = cong ⟪_⟫ (enc-⟨⟩ m)

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

-- A run of the one-tick grade is not empty.

tick-nonempty : ∀ x y → x ∈ table (R.of-dur 1) → y ∈ table R.⊤ → x ++ y ≡ [] → ⊥
tick-nonempty x y x∈ _ eq with trans (sym (cong (_++ y) (R.∈tick⁻ 1 x x∈))) eq
... | ()

private
  module RG = Grade R.right-sided
  module SG = Grade SR.right-sided

  -- The argument at variables `d` and `t` for `R.of-dur 1` and `R.⊤`,
  -- so that no order is decided by unfolding their tables.
  no-morphism-at : (f : SR.right-sided →ᵍ R.right-sided) (d t : Regular)
    → _→ᵍ_.map f (SR.of-durᵖ 1) ≾ d
    → t ≾ _→ᵍ_.map f SG.⊤ → _→ᵍ_.map f SG.⊤ ≾ t
    → (∀ x y → x ∈ table d → y ∈ table t → x ++ y ≡ [] → ⊥) → [] ∈ table t
    → ⊥
  no-morphism-at f d t map-d t-map map-t nonempty []∈t =
    R.∈·-elim d t (λ v → v ≡ [] → ⊥) [] []∈ nonempty refl
    where
    open _→ᵍ_ f

    -- `{ ⟨1⟩ } · any-run` is above `any-run`. Each step is stated at the
    -- exact terms it relates, the carriers' equations being `refl`.
    top : t ≾ d ·ᴿ t
    top = R≾-trans t M (d ·ᴿ t) t₁
            (R≾-trans M (map (SR.of-durᵖ 1) ·ᴿ map SR.any-run) (d ·ᴿ t) t₂
              (R≾-trans (map (SR.of-durᵖ 1) ·ᴿ map SR.any-run) (d ·ᴿ map SR.any-run)
                        (d ·ᴿ t) t₃ t₄))
      where
        R≾-trans : ∀ a b c → a ≾ b → b ≾ c → a ≾ c
        R≾-trans a b c = RG.≾-trans {a} {b} {c}
        M = map (SR.of-durᵖ 1 SG.· SR.any-run)
        e₁ : SG.⊤ ≡ SR.of-durᵖ 1 SG.· SR.any-run
        e₁ = refl
        t₁ : t ≾ map (SR.of-durᵖ 1 SG.· SR.any-run)
        t₁ = subst (λ c → t ≾ map c) e₁ t-map
        t₂ : map (SR.of-durᵖ 1 SG.· SR.any-run) ≾ map (SR.of-durᵖ 1) ·ᴿ map SR.any-run
        t₂ = proj₁ (map-· {SR.of-durᵖ 1} {SR.any-run})
        t₃ : map (SR.of-durᵖ 1) ·ᴿ map SR.any-run ≾ d ·ᴿ map SR.any-run
        t₃ = RG.·-monoˡ-≾ {map SR.any-run} {map (SR.of-durᵖ 1)} {d} map-d
        t₄ : d ·ᴿ map SR.any-run ≾ d ·ᴿ t
        t₄ = RG.·-monoʳ-≾ {d} {map SR.any-run} {t}
               (subst (λ c → map c ≾ t) (sym e₂) map-t)
          where
            e₂ : SR.any-run ≡ SG.⊤
            e₂ = refl

    []∈ : [] ∈ table (d ·ᴿ t)
    []∈ = R.≾⇒⊆ t (d ·ᴿ t) top [] []∈t

no-morphism : ¬ (SR.right-sided →ᵍ R.right-sided)
no-morphism f =
  no-morphism-at f (R.of-dur 1) R.⊤ (proj₁ map-of-dur) (proj₂ map-⊤) (proj₁ map-⊤)
    tick-nonempty (R.∈⊤ [])
  where open _→ᵍ_ f
