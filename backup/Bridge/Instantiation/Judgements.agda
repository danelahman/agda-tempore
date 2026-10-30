------------------------------------------------------------------
-- Declarative satisfaction of hypotheses                       --
--                                                              --
-- A declarative instance `σ` satisfies `Q` (`σ ⊨ᴰ Q`) when     --
-- each atom of `Q` holds in the closed calculus at its         --
-- interpretation: an eternality atom as `Eternal`, a subtyping --
-- atom as `_<:ᵛ_`, an ordering in the grade's order, and a     --
-- var-rule disjunction as a sum.                               --
--                                                              --
-- Entailment is sound for it: what `Q` entails holds at every  --
-- instance satisfying `Q` (`sound-≾ᵣ`, `sound-≾ₑ`, `sound-⊩ᴱ`, --
-- `sound-<:ᵛ`, `sound-<:ᶜ`, `sound-VarOK`). Grade entailment   --
-- being semantic consequence, its soundness is its definition  --
-- at the closed instance `⌜ σ ⌝ˢ`, which satisfies the grade   --
-- part of `Q` (`⌜⌝ˢ-⊨ᵍ`) and whose values are the meanings at  --
-- `σ` (`⌜⌝ˢ-valʳ`, `⌜⌝ˢ-valᵉ`). A membership in an open        --
-- context is one in its interpretation (`⟦_⟧ˣ`), and a handler --
-- clause's weakened hypotheses hold at every extension of a    --
-- satisfying instance (`⊨ᴰ-,ᵉ`).                               --
------------------------------------------------------------------

open import Data.Fin using (toℕ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec) renaming (map to mapᵛ; [] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module Bridge.Instantiation.Judgements (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Language.Types                  S
open import ClosedCalculus.Syntax.Contexts  S
open import ClosedCalculus.Syntax.Subtyping S
import ClosedCalculus.Syntax.Erasure S as CE

open import OpenCalculus.Syntax.Grades   S
open import OpenCalculus.Syntax.Types    S
open import OpenCalculus.Syntax.Contexts S
open import OpenCalculus.Syntax.Subst    S
open import OpenCalculus.Hypotheses      S

open import Bridge.Instantiation.Types S

------------------------------------------------------------------------
-- Satisfaction

-- Grade orderings hold when each does in the grade's order

infix 4 _⊨ᴰᵒ_ _⊨ᴰ⟨_⟩_ _⊨ᴰᴼ_ _⊨ᴰ_

record _⊨ᴰᵒ_ {Θ : Scope} (σ : DInst Θ) (o : Ords Θ) : Set where
  constructor mk⊨ᴰᵒ
  field
    ⊨ors : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors o → ⟦ ρ ⟧ʳ σ ≾ᵣ ⟦ ρ' ⟧ʳ σ
    ⊨oes : ∀ {ε ε'} → (ε , ε') ∈ oes o → ⟦ ε ⟧ᵉ σ ≾ₑ ⟦ ε' ⟧ᵉ σ

open _⊨ᴰᵒ_ public

-- A quantified ordering `∀ᵉ j₁ … jₖ. O` holds when `O` does at every
-- extension by grades for its rigids

_⊨ᴰ⟨_⟩_ : ∀ {Θ} → DInst Θ → (k : ℕ) → Ords (Θ +eⁿ k) → Set
σ ⊨ᴰ⟨ zero ⟩  B = σ ⊨ᴰᵒ B
σ ⊨ᴰ⟨ suc k ⟩ B = (c : E) → (σ ,ᵉᴰ c) ⊨ᴰ⟨ k ⟩ B

_⊨ᴰᴼ_ : ∀ {Θ} → DInst Θ → QOrd Θ → Set
σ ⊨ᴰᴼ O = σ ⊨ᴰ⟨ rigids O ⟩ body O

-- A satisfying instance: each hypothesis holds, a quantified one at
-- every grade for its rigids

record _⊨ᴰ_ {Θ : Scope} (σ : DInst Θ) (Q : Hyps Θ) : Set where
  constructor mk⊨ᴰ
  field
    ⊨ets  : ∀ {α} → α ∈ ets Q → Eternal (ty σ α)
    ⊨subᵥ : ∀ {α β} → (α , β) ∈ subᵥ Q → ty σ α <:ᵛ ty σ β
    ⊨ordᵣ : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → ⟦ ρ ⟧ʳ σ ≾ᵣ ⟦ ρ' ⟧ʳ σ
    ⊨ordₑ : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → ⟦ ε ⟧ᵉ σ ≾ₑ ⟦ ε' ⟧ᵉ σ
    ⊨disj : ∀ {A ρ} → (A , ρ) ∈ disj Q → Eternal (⟦ A ⟧ᵛ σ) ⊎ (⟦ ρ ⟧ʳ σ ≾ᵣ uᵣ)
    ⊨qhyps : ∀ {O} → O ∈ qhyps Q → σ ⊨ᴰᴼ O

open _⊨ᴰ_ public

⊨ᴰ-∅ : ∀ {Θ} {σ : DInst Θ} → σ ⊨ᴰ ∅ᴴ
⊨ᴰ-∅ = mk⊨ᴰ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

-- Grade orderings along pointwise equal instances, at an instance of
-- the rigids, and along a substitution

⊨ᴰᵒ-≗ : ∀ {Θ} {σ σ' : DInst Θ} {o : Ords Θ} → σ ≗ᴰ σ' → σ ⊨ᴰᵒ o → σ' ⊨ᴰᵒ o
⊨ᴰᵒ-≗ p s = mk⊨ᴰᵒ
  (λ {ρ} {ρ'} m → subst₂ _≾ᵣ_ (⟦≗⟧ʳ p ρ) (⟦≗⟧ʳ p ρ') (⊨ors s m))
  (λ {ε} {ε'} m → subst₂ _≾ₑ_ (⟦≗⟧ᵉ p ε) (⟦≗⟧ᵉ p ε') (⊨oes s m))

⊨ᴰ⟨⟩-≗ : ∀ {Θ} {σ σ' : DInst Θ} → (k : ℕ) → {B : Ords (Θ +eⁿ k)}
       → σ ≗ᴰ σ' → σ ⊨ᴰ⟨ k ⟩ B → σ' ⊨ᴰ⟨ k ⟩ B
⊨ᴰ⟨⟩-≗ zero    p s = ⊨ᴰᵒ-≗ p s
⊨ᴰ⟨⟩-≗ (suc k) p s = λ c → ⊨ᴰ⟨⟩-≗ k (≗ᴰ-,ᵉ p c) (s c)

⊨ᴰ⟨⟩-at : ∀ {Θ k} {σ : DInst Θ} {B : Ords (Θ +eⁿ k)}
        → σ ⊨ᴰ⟨ k ⟩ B → (cs : Vec E k) → (σ ,ᵉᴰⁿ cs) ⊨ᴰᵒ B
⊨ᴰ⟨⟩-at s []ᵛ        = s
⊨ᴰ⟨⟩-at s (c ∷ᵛ cs) = ⊨ᴰ⟨⟩-at (s c) cs

⊨ᴰ⟨⟩-[] : ∀ {Θ Θ'} → (k : ℕ) → (τ : Subst Θ Θ') → (σ : DInst Θ') → {B : Ords (Θ +eⁿ k)}
        → (τ ⨟ᴰ σ) ⊨ᴰ⟨ k ⟩ B → σ ⊨ᴰ⟨ k ⟩ (B [ τ ↑ᵉⁿ k ]ᴼ)
⊨ᴰ⟨⟩-[] zero τ σ {B} s = mk⊨ᴰᵒ rd ed
  where
    rd : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors (B [ τ ]ᴼ) → ⟦ ρ ⟧ʳ σ ≾ᵣ ⟦ ρ' ⟧ʳ σ
    rd m with ∈-map⁻ (mapᵖ (_[ τ ]ʳ)) m
    ... | (x , y) , m₀ , refl = subst₂ _≾ᵣ_ (sym (⟦[]⟧ʳ τ σ x)) (sym (⟦[]⟧ʳ τ σ y)) (⊨ors s m₀)

    ed : ∀ {ε ε'} → (ε , ε') ∈ oes (B [ τ ]ᴼ) → ⟦ ε ⟧ᵉ σ ≾ₑ ⟦ ε' ⟧ᵉ σ
    ed m with ∈-map⁻ (mapᵖ (_[ τ ]ᵉ)) m
    ... | (x , y) , m₀ , refl = subst₂ _≾ₑ_ (sym (⟦[]⟧ᵉ τ σ x)) (sym (⟦[]⟧ᵉ τ σ y)) (⊨oes s m₀)
⊨ᴰ⟨⟩-[] (suc k) τ σ s c =
  ⊨ᴰ⟨⟩-[] k (τ ↑ᵉ) (σ ,ᵉᴰ c) (⊨ᴰ⟨⟩-≗ k (≗ᴰ-sym (↑ᵉ-⨟ᴰ τ σ c)) (s c))

------------------------------------------------------------------------
-- Soundness of convertibility and entailed ordering

-- A declarative instance is the meaning of the closed instance sending
-- each variable to a constant: on grades, a value there is a meaning
-- at it

⌜⌝ˢ-valʳ : ∀ {Θ} → (σ : DInst Θ) → (ρ : RExp Θ) → valʳ (ρ [ ⌜ σ ⌝ˢ ]ʳ) ≡ ⟦ ρ ⟧ʳ σ
⌜⌝ˢ-valʳ σ ρ = trans (sym (⟦⟧∅-valʳ (ρ [ ⌜ σ ⌝ˢ ]ʳ)))
                     (trans (⟦[]⟧ʳ ⌜ σ ⌝ˢ ∅ᴰ ρ) (⟦≗⟧ʳ ⌞⌜ σ ⌝ˢ⌟ ρ))

⌜⌝ˢ-valᵉ : ∀ {Θ} → (σ : DInst Θ) → (ε : EExp Θ) → valᵉ (ε [ ⌜ σ ⌝ˢ ]ᵉ) ≡ ⟦ ε ⟧ᵉ σ
⌜⌝ˢ-valᵉ σ ε = trans (sym (⟦⟧∅-valᵉ (ε [ ⌜ σ ⌝ˢ ]ᵉ)))
                     (trans (⟦[]⟧ᵉ ⌜ σ ⌝ˢ ∅ᴰ ε) (⟦≗⟧ᵉ ⌞⌜ σ ⌝ˢ⌟ ε))

-- and satisfies the grade part of what the declarative instance
-- satisfies, a quantified ordering at each closed instance of its
-- rigids, their values

⌜⌝ˢ-⊨ᵍ : ∀ {Θ} {σ : DInst Θ} {Q : Hyps Θ} → σ ⊨ᴰ Q → ⌜ σ ⌝ˢ ⊨ᵍ Q
⌜⌝ˢ-⊨ᵍ {Θ} {σ} {Q} s = mk⊨ᵍ oR oE qh
  where
    oR : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ Q → valʳ (ρ [ ⌜ σ ⌝ˢ ]ʳ) ≾ᵣ valʳ (ρ' [ ⌜ σ ⌝ˢ ]ʳ)
    oR {ρ} {ρ'} m = subst₂ _≾ᵣ_ (sym (⌜⌝ˢ-valʳ σ ρ)) (sym (⌜⌝ˢ-valʳ σ ρ')) (⊨ordᵣ s m)

    oE : ∀ {ε ε'} → (ε , ε') ∈ ordₑ Q → valᵉ (ε [ ⌜ σ ⌝ˢ ]ᵉ) ≾ₑ valᵉ (ε' [ ⌜ σ ⌝ˢ ]ᵉ)
    oE {ε} {ε'} m = subst₂ _≾ₑ_ (sym (⌜⌝ˢ-valᵉ σ ε)) (sym (⌜⌝ˢ-valᵉ σ ε')) (⊨ordₑ s m)

    qh : ∀ {O} → O ∈ qhyps Q → (es : Vec (EExp ∅ˢ) (rigids O)) → (⌜ σ ⌝ˢ ,ᵉⁿ es) ⊨ᵒ body O
    qh {O} m es = mk⊨ᵒ r e
      where
        cs = mapᵛ (λ x → ⟦ x ⟧ᵉ ∅ᴰ) es
        d  = ⊨ᴰ⟨⟩-at (⊨qhyps s m) cs

        p : ((⌜ σ ⌝ˢ ,ᵉⁿ es) ⨟ᴰ ∅ᴰ) ≗ᴰ (σ ,ᵉᴰⁿ cs)
        p = ≗ᴰ-trans (,ᵉⁿ-⨟ᴰ ⌜ σ ⌝ˢ es ∅ᴰ) (≗ᴰ-,ᵉᴰⁿ ⌞⌜ σ ⌝ˢ⌟ cs)

        valeqʳ : (x : RExp (Θ +eⁿ rigids O)) → valʳ (x [ ⌜ σ ⌝ˢ ,ᵉⁿ es ]ʳ) ≡ ⟦ x ⟧ʳ (σ ,ᵉᴰⁿ cs)
        valeqʳ x = trans (sym (⟦⟧∅-valʳ (x [ ⌜ σ ⌝ˢ ,ᵉⁿ es ]ʳ)))
                         (trans (⟦[]⟧ʳ (⌜ σ ⌝ˢ ,ᵉⁿ es) ∅ᴰ x) (⟦≗⟧ʳ p x))

        valeqᵉ : (x : EExp (Θ +eⁿ rigids O)) → valᵉ (x [ ⌜ σ ⌝ˢ ,ᵉⁿ es ]ᵉ) ≡ ⟦ x ⟧ᵉ (σ ,ᵉᴰⁿ cs)
        valeqᵉ x = trans (sym (⟦⟧∅-valᵉ (x [ ⌜ σ ⌝ˢ ,ᵉⁿ es ]ᵉ)))
                         (trans (⟦[]⟧ᵉ (⌜ σ ⌝ˢ ,ᵉⁿ es) ∅ᴰ x) (⟦≗⟧ᵉ p x))

        r : ∀ {ρ ρ'} → (ρ , ρ') ∈ ors (body O)
          → valʳ (ρ [ ⌜ σ ⌝ˢ ,ᵉⁿ es ]ʳ) ≾ᵣ valʳ (ρ' [ ⌜ σ ⌝ˢ ,ᵉⁿ es ]ʳ)
        r {ρ} {ρ'} mφ = subst₂ _≾ᵣ_ (sym (valeqʳ ρ)) (sym (valeqʳ ρ')) (⊨ors d mφ)

        e : ∀ {ε ε'} → (ε , ε') ∈ oes (body O)
          → valᵉ (ε [ ⌜ σ ⌝ˢ ,ᵉⁿ es ]ᵉ) ≾ₑ valᵉ (ε' [ ⌜ σ ⌝ˢ ,ᵉⁿ es ]ᵉ)
        e {ε} {ε'} mφ = subst₂ _≾ₑ_ (sym (valeqᵉ ε)) (sym (valeqᵉ ε')) (⊨oes d mφ)

-- Entailment is semantic consequence, so it is sound at the closed
-- instance a declarative one determines

sound-≡̂ᵣ : ∀ {Θ} {ρ ρ' : RExp Θ} → (σ : DInst Θ) → ρ ≡̂ᵣ ρ' → ⟦ ρ ⟧ʳ σ ≃ᵣ ⟦ ρ' ⟧ʳ σ
sound-≡̂ᵣ {ρ = ρ} {ρ'} σ p =
  subst₂ _≃ᵣ_ (⌜⌝ˢ-valʳ σ ρ) (⌜⌝ˢ-valʳ σ ρ') (≡̂ᵣ-run p ⌜ σ ⌝ˢ)

sound-≡̂ₑ : ∀ {Θ} {ε ε' : EExp Θ} → (σ : DInst Θ) → ε ≡̂ₑ ε' → ⟦ ε ⟧ᵉ σ ≃ₑ ⟦ ε' ⟧ᵉ σ
sound-≡̂ₑ {ε = ε} {ε'} σ p =
  subst₂ _≃ₑ_ (⌜⌝ˢ-valᵉ σ ε) (⌜⌝ˢ-valᵉ σ ε') (≡̂ₑ-run p ⌜ σ ⌝ˢ)

sound-≾ᵣ : ∀ {Θ} {σ : DInst Θ} {Q : Hyps Θ} {ρ ρ' : RExp Θ}
         → σ ⊨ᴰ Q → Q ⊩ ρ ≾̂ᵣ ρ' → ⟦ ρ ⟧ʳ σ ≾ᵣ ⟦ ρ' ⟧ʳ σ
sound-≾ᵣ {σ = σ} {ρ = ρ} {ρ'} s p =
  subst₂ _≾ᵣ_ (⌜⌝ˢ-valʳ σ ρ) (⌜⌝ˢ-valʳ σ ρ') (runᵣ p ⌜ σ ⌝ˢ (⌜⌝ˢ-⊨ᵍ s))

sound-≾ₑ : ∀ {Θ} {σ : DInst Θ} {Q : Hyps Θ} {ε ε' : EExp Θ}
         → σ ⊨ᴰ Q → Q ⊩ ε ≾̂ₑ ε' → ⟦ ε ⟧ᵉ σ ≾ₑ ⟦ ε' ⟧ᵉ σ
sound-≾ₑ {σ = σ} {ε = ε} {ε'} s p =
  subst₂ _≾ₑ_ (⌜⌝ˢ-valᵉ σ ε) (⌜⌝ˢ-valᵉ σ ε') (runₑ p ⌜ σ ⌝ˢ (⌜⌝ˢ-⊨ᵍ s))

------------------------------------------------------------------------
-- Soundness of the type-level judgements

module _ {Θ : Scope} {σ : DInst Θ} {Q : Hyps Θ} (s : σ ⊨ᴰ Q) where

  sound-⊩ᵗᵛ : ∀ {α β} → Q ⊩ᵗᵛ α ≾ β → ty σ α <:ᵛ ty σ β
  sound-⊩ᵗᵛ (reflᵗᵛ {α})  = <:ᵛ-refl (ty σ α)
  sound-⊩ᵗᵛ (hypᵗᵛ m)     = ⊨subᵥ s m
  sound-⊩ᵗᵛ (transᵗᵛ p q) = <:ᵛ-trans (sound-⊩ᵗᵛ p) (sound-⊩ᵗᵛ q)

  sound-⊩ᴱ : {A : OVType Θ} → Q ⊩ᴱ A → Eternal (⟦ A ⟧ᵛ σ)
  sound-⊩ᴱ (et-hyp m)     = ⊨ets s m
  sound-⊩ᴱ (et-subˡ p et) = <:ᵛ-eternalˡ (sound-⊩ᵗᵛ p) (sound-⊩ᴱ et)
  sound-⊩ᴱ (et-subʳ p et) = <:ᵛ-eternalʳ (sound-⊩ᵗᵛ p) (sound-⊩ᴱ et)
  sound-⊩ᴱ (Baseₑ p)      = Baseₑ p
  sound-⊩ᴱ Unitₑ          = Unitₑ
  sound-⊩ᴱ Boolₑ          = Boolₑ
  sound-⊩ᴱ Natₑ           = Natₑ
  sound-⊩ᴱ (p |×|ₑ q)     = sound-⊩ᴱ p |×|ₑ sound-⊩ᴱ q
  sound-⊩ᴱ (p |+|ₑ q)     = sound-⊩ᴱ p |+|ₑ sound-⊩ᴱ q
  sound-⊩ᴱ (|List|ₑ p)    = |List|ₑ (sound-⊩ᴱ p)
  sound-⊩ᴱ Emptyₑ         = Emptyₑ

  sound-<:ᵛ : {A B : OVType Θ} → Q ∣ A <:̂ᵛ B → ⟦ A ⟧ᵛ σ <:ᵛ ⟦ B ⟧ᵛ σ
  sound-<:ᶜ : {C D : OCType Θ} → Q ∣ C <:̂ᶜ D → ⟦ C ⟧ᶜ σ <:ᶜ ⟦ D ⟧ᶜ σ

  sound-<:ᵛ (tvarₛ p)   = sound-⊩ᵗᵛ p
  sound-<:ᵛ (Baseₛ p)   = Baseₛ p
  sound-<:ᵛ Unitₛ       = Unitₛ
  sound-<:ᵛ Boolₛ       = Boolₛ
  sound-<:ᵛ Natₛ        = Natₛ
  sound-<:ᵛ (p |×|ₛ q)  = sound-<:ᵛ p |×|ₛ sound-<:ᵛ q
  sound-<:ᵛ (p |+|ₛ q)  = sound-<:ᵛ p |+|ₛ sound-<:ᵛ q
  sound-<:ᵛ (|List|ₛ p) = |List|ₛ (sound-<:ᵛ p)
  sound-<:ᵛ Emptyₛ      = Emptyₛ
  sound-<:ᵛ (p ⇒ₛ q)    = sound-<:ᵛ p ⇒ₛ sound-<:ᶜ q
  sound-<:ᵛ (p ⇛ₛ q)    = <:ᵛ-refl handlerᴰ
  sound-<:ᵛ ([ p ]ₛ q)  = [ sound-≾ᵣ s p ]ₛ sound-<:ᵛ q

  sound-<:ᶜ (p ‼ₛ q) = sound-<:ᵛ p ‼ₛ sound-≾ₑ s q

  -- the var-rule disjunction

  sound-VarOK : {A : OVType Θ} {ρ : RExp Θ} → VarOK Q A ρ
              → Eternal (⟦ A ⟧ᵛ σ) ⊎ (⟦ ρ ⟧ʳ σ ≾ᵣ uᵣ)
  sound-VarOK (et-ok et) = inj₁ (sound-⊩ᴱ et)
  sound-VarOK (≾ᵘ-ok le) = inj₂ (sound-≾ᵣ s le)
  sound-VarOK (hyp-ok m q) with ⊨disj s m
  ... | inj₁ et = inj₁ et
  ... | inj₂ le = inj₂ (≾ᵣ-trans (sound-≾ᵣ s q) le)
  sound-VarOK (subˡ-ok p ok) with sound-VarOK ok
  ... | inj₁ et = inj₁ (<:ᵛ-eternalˡ (sound-<:ᵛ p) et)
  ... | inj₂ le = inj₂ le
  sound-VarOK (subʳ-ok p ok) with sound-VarOK ok
  ... | inj₁ et = inj₁ (<:ᵛ-eternalʳ (sound-<:ᵛ p) et)
  ... | inj₂ le = inj₂ le
  sound-VarOK (ok₁ |×|-ok ok₂) with sound-VarOK ok₁ | sound-VarOK ok₂
  ... | inj₁ et₁ | inj₁ et₂ = inj₁ (et₁ |×|ₑ et₂)
  ... | inj₂ le  | _        = inj₂ le
  ... | inj₁ _   | inj₂ le  = inj₂ le
  sound-VarOK (ok₁ |+|-ok ok₂) with sound-VarOK ok₁ | sound-VarOK ok₂
  ... | inj₁ et₁ | inj₁ et₂ = inj₁ (et₁ |+|ₑ et₂)
  ... | inj₂ le  | _        = inj₂ le
  ... | inj₁ _   | inj₂ le  = inj₂ le
  sound-VarOK (|List|-ok ok) with sound-VarOK ok
  ... | inj₁ et = inj₁ (|List|ₑ et)
  ... | inj₂ le = inj₂ le
  sound-VarOK (⊔-ok q ok₁ ok₂) with sound-VarOK ok₁ | sound-VarOK ok₂
  ... | inj₁ et  | _        = inj₁ et
  ... | inj₂ _   | inj₁ et  = inj₁ et
  ... | inj₂ le₁ | inj₂ le₂ = inj₂ (≾ᵣ-trans (sound-≾ᵣ s q) (⊔ᵣ-lub le₁ le₂))

------------------------------------------------------------------------
-- Memberships

⟦_⟧ˣ : ∀ {Θ n} {Γ : OCtx Θ n} {A : OVType Θ} {ρ : RExp Θ}
     → A ∈̂[ ρ ] Γ → {σ : DInst Θ} → ⟦ A ⟧ᵛ σ ∈[ ⟦ ρ ⟧ʳ σ ] ⟦ Γ ⟧ᶜᵗˣ σ
⟦ Hd ⟧ˣ       = Hd
⟦ Tl-∷ x ⟧ˣ   = Tl-∷ ⟦ x ⟧ˣ
⟦ Tl-⟨⟩ x ⟧ˣ  = Tl-⟨⟩ ⟦ x ⟧ˣ

-- at the same position

⟦⟧ˣ-pos : ∀ {Θ n} {Γ : OCtx Θ n} {A : OVType Θ} {ρ : RExp Θ} {σ : DInst Θ}
        → (x : A ∈̂[ ρ ] Γ) → CE.var-pos (⟦ x ⟧ˣ {σ}) ≡ toℕ (var-pos x)
⟦⟧ˣ-pos Hd        = refl
⟦⟧ˣ-pos (Tl-∷ x)  = cong suc (⟦⟧ˣ-pos x)
⟦⟧ˣ-pos (Tl-⟨⟩ x) = ⟦⟧ˣ-pos x

------------------------------------------------------------------------
-- A handler clause is typed under `wkᵉ-H Q`, which every extension of
-- an instance satisfying `Q` satisfies

⊨ᴰ-,ᵉ : ∀ {Θ} {σ : DInst Θ} {Q : Hyps Θ} → (c : E) → σ ⊨ᴰ Q → (σ ,ᵉᴰ c) ⊨ᴰ wkᵉ-H Q
⊨ᴰ-,ᵉ {Θ} {σ} {Q} c s = mk⊨ᴰ ets' subᵥ' ordᵣ' ordₑ' disj' qhyps'
  where
    ets' : ∀ {α} → α ∈ ets (wkᵉ-H Q) → Eternal (ty (σ ,ᵉᴰ c) α)
    ets' m with ∈-map⁻ (wkᵉ-tv Θ) m
    ... | _ , m₀ , refl = ⊨ets s m₀

    subᵥ' : ∀ {α β} → (α , β) ∈ subᵥ (wkᵉ-H Q) → ty (σ ,ᵉᴰ c) α <:ᵛ ty (σ ,ᵉᴰ c) β
    subᵥ' m with ∈-map⁻ (mapᵖ (wkᵉ-tv Θ)) m
    ... | _ , m₀ , refl = ⊨subᵥ s m₀

    ordᵣ' : ∀ {ρ ρ'} → (ρ , ρ') ∈ ordᵣ (wkᵉ-H Q)
          → ⟦ ρ ⟧ʳ (σ ,ᵉᴰ c) ≾ᵣ ⟦ ρ' ⟧ʳ (σ ,ᵉᴰ c)
    ordᵣ' m with ∈-map⁻ (mapᵖ wkᵉ-r) m
    ... | (ρ₀ , ρ₀') , m₀ , refl =
      subst₂ _≾ᵣ_ (sym (⟦wkᵉ⟧ʳ σ c ρ₀)) (sym (⟦wkᵉ⟧ʳ σ c ρ₀')) (⊨ordᵣ s m₀)

    ordₑ' : ∀ {ε ε'} → (ε , ε') ∈ ordₑ (wkᵉ-H Q)
          → ⟦ ε ⟧ᵉ (σ ,ᵉᴰ c) ≾ₑ ⟦ ε' ⟧ᵉ (σ ,ᵉᴰ c)
    ordₑ' m with ∈-map⁻ (mapᵖ wkᵉ-e) m
    ... | (ε₀ , ε₀') , m₀ , refl =
      subst₂ _≾ₑ_ (sym (⟦wkᵉ⟧ᵉ σ c ε₀)) (sym (⟦wkᵉ⟧ᵉ σ c ε₀')) (⊨ordₑ s m₀)

    disj' : ∀ {A ρ} → (A , ρ) ∈ disj (wkᵉ-H Q)
          → Eternal (⟦ A ⟧ᵛ (σ ,ᵉᴰ c)) ⊎ (⟦ ρ ⟧ʳ (σ ,ᵉᴰ c) ≾ᵣ uᵣ)
    disj' m with ∈-map⁻ (mapᵈ wkᵉ-v wkᵉ-r) m
    ... | (A₀ , ρ₀) , m₀ , refl =
      subst₂ (λ X r → Eternal X ⊎ (r ≾ᵣ uᵣ)) (sym (⟦wkᵉ⟧ᵛ σ c A₀)) (sym (⟦wkᵉ⟧ʳ σ c ρ₀))
             (⊨disj s m₀)

    qhyps' : ∀ {O} → O ∈ qhyps (wkᵉ-H Q) → (σ ,ᵉᴰ c) ⊨ᴰᴼ O
    qhyps' m with ∈-map⁻ (_[ wkˢᵉ ]ᵠ) m
    ... | O₀ , m₀ , refl =
      ⊨ᴰ⟨⟩-[] (rigids O₀) wkˢᵉ (σ ,ᵉᴰ c) (⊨ᴰ⟨⟩-≗ (rigids O₀) ≗ᴰ-refl (⊨qhyps s m₀))
