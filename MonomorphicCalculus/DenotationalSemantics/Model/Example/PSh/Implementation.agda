---------------------------------------------------------------------------
-- Running the operations, on presheaves.                                --
--                                                                       --
-- The graded monad morphism from the free tree monad into the free tick --
-- monad, determined by a semantic implementation of the operations      --
--                                                                       --
--   op-semᵐ op : ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ param op ⟧ᵍ →ᵖ ⟦ arity op ⟧ᵍ --
--                                                                       --
-- On trees it is the identity on leaves, delays and coercions; an       --
-- operation node becomes a tick at the operation's grade, its           --
-- continuation fed the value the implementation computes.               --
---------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base as B
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future as F
import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Past as P

module MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Implementation
         (S : LanguageSpec)
         (Wld : World (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (GTy : GroundTypes S (B.PShCat (LanguageSpec.Grades S) Wld)
                              (F.PShFut (LanguageSpec.Grades S) Wld))
       where

open import Data.Product using (_,_)

open import Util.Equality

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops
open World Wld
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Base Grades Wld
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Future Grades Wld
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Past Grades Wld
  hiding (⊑ρ∘ᵘ)
open import Relation.Binary.Construct.Closure.Equivalence using (return)
open GroundTypes GTy

open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Core S Wld GTy
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Monad.Effects S Wld GTy
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.TickMonad S Wld
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.PSh.Modality.Adjunction Grades Wld
  using (η⊣)

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open Category PShCat using (_×ᵐ_; ⟨_,_⟩ᵐ; curryᵐ)

-- The semantic implementations of the operations.

OpSemᵐ : Set
OpSemᵐ = (op : Op) → ⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ param op ⟧ᵍ →ᵖ ⟦ arity op ⟧ᵍ

module _ (op-semᵐ : OpSemᵐ) where

  -- The arity value the implementation returns, at a world the operation's
  -- continuation reaches.

  semᵃ : ∀ {w w'} → (op : Op) → w ⊑[ mapᵉ (op-grade op) ] w'
       → carrier ⟦ param op ⟧ᵍ w → carrier ⟦ arity op ⟧ᵍ w'
  semᵃ op q v = app (op-semᵐ op) (mk⟨⟩ q v)

  -- Its naturality: the value at a later world is the transported one.

  semᵃ-nat : ∀ {w w' w''} → (op : Op) → (q : w ⊑[ mapᵉ (op-grade op) ] w')
           → (r : w' ⊑[ uᵣ ] w'') → (v : carrier ⟦ param op ⟧ᵍ w)
           → _≈_ ⟦ arity op ⟧ᵍ (semᵃ op (⊑ρ∘ᵘ q r) v)
                               (transport ⟦ arity op ⟧ᵍ r (semᵃ op q v))
  semᵃ-nat op q r v = nat (op-semᵐ op) r (mk⟨⟩ q v)

  -- and its congruence: `≈`-equal parameters give `≈`-equal arity values

  semᵃ-cong : ∀ {w w'} → (op : Op) → (q : w ⊑[ mapᵉ (op-grade op) ] w')
            → {v v' : carrier ⟦ param op ⟧ᵍ w}
            → _≈_ ⟦ param op ⟧ᵍ v v'
            → _≈_ ⟦ arity op ⟧ᵍ (semᵃ op q v) (semᵃ op q v')
  semᵃ-cong op q {v} ev =
    app-cong (op-semᵐ op)
      (return (⊑-refl , ≈-trans ⟦ param op ⟧ᵍ (transport-refl ⟦ param op ⟧ᵍ v) ev))

  -- THE MORPHISM

  mutual

    -- `TERMINATING`: every call is at subtrees or witnesses stored in the matched
    -- tree or proof (or in the trees it relates), possibly joined by `≈ᵗ-trans`, or
    -- is `implˢ-nat`'s call at its own tree; the checker cannot see that
    -- `transportᵗ r (k q)` (from a stored `kn`) is no larger than `k q`.

    {-# TERMINATING #-}

    implˢ : ∀ {A ε w} → Tˢ A ε w → Tᵏˢ A ε w
    implˢ (leaf x) = leaf x
    implˢ (op-node op v k kc kn) =
      tick-node (op-grade op)
        (λ q → implˢ (k q (semᵃ op q v)))
        (λ q r → ≈ᵏ-trans
          (implˢ-cong
            (≈ᵗ-trans (kc (⊑ρ∘ᵘ q r) (semᵃ-nat op q r v))
                      (kn q r (semᵃ op q v))))
          (implˢ-nat r (k q (semᵃ op q v))))
    implˢ (delay-node τ k kn) =
      tick-node (of-durᵉ τ)
        (λ q → implˢ (k q))
        (λ q r → ≈ᵏ-trans (implˢ-cong (kn q r)) (implˢ-nat r (k q)))
    implˢ (sub p t) = sub p (implˢ t)

    implˢ-cong : ∀ {A ε w} {t t' : Tˢ A ε w} → t ≈ᵗ t' → implˢ t ≈ᵏ implˢ t'
    implˢ-cong (leaf-≈ e)   = leaf-≈ e
    -- the two nodes' parameters are `≈`-equal, so the implementation returns
    -- `≈`-equal arity values; the stored congruence witness `kc` bridges them
    implˢ-cong (op-≈ {op = op} {v' = v'} {kc = kc} ev ek) =
      tick-≈ (λ q → implˢ-cong
        (≈ᵗ-trans (kc q (semᵃ-cong op q ev)) (ek q (semᵃ op q v'))))
    implˢ-cong (delay-≈ ek) = tick-≈ (λ q → implˢ-cong (ek q))
    implˢ-cong (sub-≈ et)   = sub-≈ (implˢ-cong et)
    implˢ-cong sub-u        = sub-uᵏ _ _
    implˢ-cong sub-∘        = sub-∘ᵏ _ _ _ _
    implˢ-cong sub-delay    = sub-tick
    implˢ-cong sub-op       = sub-tick
    -- a delay implements as a tick, so the two delay collapses implement as
    -- the two tick collapses; the split witnesses agree by `⊑-irrelevant`
    implˢ-cong (delay-zero {k = k} {q₀ = q₀} e) = tick-u {q₀ = q₀} of-durᵉ-zero e
    implˢ-cong (delay-plus {τ₁ = τ₁} {τ₂ = τ₂} {k = k} {kn = kn} hk e) =
      tick-· of-durᵉ-plus
        (λ q₁ q₂ → ≈ᵏ-trans (implˢ-cong (hk q₁ q₂))
                     (≡→≈ᵏ (cong (λ z → implˢ (k z)) (⊑-irrelevant _ _))))
        e
    implˢ-cong (≈ᵗ-sym et)  = ≈ᵏ-sym (implˢ-cong et)
    implˢ-cong (≈ᵗ-trans et et') =
      ≈ᵏ-trans (implˢ-cong et) (implˢ-cong et')


    -- The implementation commutes with a grade transport.

    implˢ-ε-substˢ : ∀ {A ε ε' w} → (e : ε ≡ ε') → (t : Tˢ A ε w)
                   → implˢ (ε-substˢ e t) ≡ ε-substᵏˢ e (implˢ t)
    implˢ-ε-substˢ refl t = refl

    implˢ-nat : ∀ {A ε w w'} (p : w ⊑[ uᵣ ] w') (t : Tˢ A ε w)
              → implˢ (transportᵗ p t) ≈ᵏ transportᵏ p (implˢ t)
    implˢ-nat {A} p (leaf x) = leaf-≈ (≈-refl A)
    -- the transported parameter, seen from the operation's future, is the
    -- untransported one seen through the composed witness
    implˢ-nat p (op-node op v k kc kn) =
      tick-≈ (λ q → implˢ-cong (kc (⊑ᵘ∘ρ p q)
        (app-cong (op-semᵐ op)
          (≈-sym (⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ param op ⟧ᵍ)
                 (return (p , ≈-refl ⟦ param op ⟧ᵍ))))))
    implˢ-nat p (delay-node τ k kn)    = tick-≈ (λ q → ≈ᵏ-refl _)
    implˢ-nat p (sub e t)              = sub-≈ (implˢ-nat p t)

  implᵐ : ∀ {A ε} → Tᵒ A ε →ᵖ Tᵏ A ε
  implᵐ = pmap implˢ implˢ-cong (λ p t → implˢ-nat p t)

  -- THE MONAD-MORPHISM LAWS

  implˢ-ε-subst : ∀ {A ε ε' w} → (e : ε ≡ ε') → (t : Tˢ A ε w)
                → implˢ (ε-substˢ e t) ≡ ε-substᵏˢ e (implˢ t)
  implˢ-ε-subst refl t = refl

  implᵐ-ηᵀ : ∀ {A} → implᵐ ∘ᵖ ηᵀ {A} ≈ᵖ ηᵏ
  implᵐ-ηᵀ x = ≈ᵏ-refl _

  implᵐ-T-≤ : ∀ {A ε ε'} → (p : ε ≾ₑ ε')
            → implᵐ {A} ∘ᵖ T-≤ p ≈ᵖ T-≤ᵏ p ∘ᵖ implᵐ
  implᵐ-T-≤ p t = ≈ᵏ-refl _

  implᵐ-ε-subst : ∀ {A ε ε'} → (e : ε ≡ ε')
                → implᵐ {A} ∘ᵖ ε-substᵀ e ≈ᵖ ε-substᵏ e ∘ᵖ implᵐ
  implᵐ-ε-subst e t = ≡→≈ᵏ (implˢ-ε-subst e t)

  -- naturality: the implementation commutes with the functorial action

  implˢ-natᶠ : ∀ {A B ε w} → (f : A →ᵖ B) → (t : Tˢ A ε w)
             → implˢ (Tˢᶠ f t) ≈ᵏ Tᵏˢᶠ f (implˢ t)
  implˢ-natᶠ {B = B} f (leaf x)        = leaf-≈ (≈-refl B)
  implˢ-natᶠ f (op-node op v k kc kn)  =
    tick-≈ (λ q → implˢ-natᶠ f (k q (semᵃ op q v)))
  implˢ-natᶠ f (delay-node τ k kn)     = tick-≈ (λ q → implˢ-natᶠ f (k q))
  implˢ-natᶠ f (sub p t)               = sub-≈ (implˢ-natᶠ f t)

  implᵐ-nat : ∀ {A B ε} → (f : A →ᵖ B)
            → implᵐ {ε = ε} ∘ᵖ Tᶠ f ≈ᵖ Tᵏᶠ f ∘ᵖ implᵐ
  implᵐ-nat f t = implˢ-natᶠ f t

  -- the multiplication

  implˢ-μ : ∀ {A ε ε' w} → (t : Tˢ (Tᵒ A ε') ε w)
          → implˢ (μˢ t) ≈ᵏ μᵏˢ (Tᵏˢᶠ implᵐ (implˢ t))
  implˢ-μ {ε' = ε'} (leaf s) = ≈ᵏ-refl _
  implˢ-μ {ε' = ε'} (op-node {ε = ε₀} op v k kc kn) =
    sub-congᵏ (tick-≈ (λ q → implˢ-μ (k q (semᵃ op q v))))
  implˢ-μ {ε' = ε'} (delay-node {ε = ε₀} τ k kn) =
    sub-congᵏ (tick-≈ (λ q → implˢ-μ (k q)))
  implˢ-μ (sub p t) = sub-≈ (implˢ-μ t)

  implᵐ-μᵀ : ∀ {A ε ε'}
           → implᵐ ∘ᵖ μᵀ {A} {ε} {ε'} ≈ᵖ μᵏ ∘ᵖ Tᵏᶠ implᵐ ∘ᵖ implᵐ
  implᵐ-μᵀ t = implˢ-μ t

  -- a delay becomes a tick at the delay's grade: the boxes sit at `of-durʳ τ`
  -- and `mapᵉ (of-durᵉ τ)`, which agree, and `[]-fun-irr` absorbs the witness

  implᵐ-delayᵀ : ∀ {A ε} → (τ : 𝔻)
               → implᵐ ∘ᵖ delayᵀ {A} {ε} τ
               ≈ᵖ tickᵏ (of-durᵉ τ)
                  ∘ᵖ []-≤ (≃ᵣ⇒≾ᵣ map-of-durᵉ)
                  ∘ᵖ [ of-durʳ τ ]ᶠ implᵐ
  implᵐ-delayᵀ τ x = tick-≈ (λ q → implˢ-cong ([]-fun-irr x _ _))

  -- and an operation becomes a tick, its continuation fed the computed value

  implᵐ-opᵀ : ∀ {X A ε} → (op : Op)
            → (v : X →ᵖ ⟦ param op ⟧ᵍ)
            → (k : (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ ⟦ arity op ⟧ᵍ) →ᵖ Tᵒ A ε)
            → implᵐ ∘ᵖ (opᵀ op
                        ∘ᵖ ⟨ v , [ mapᵉ (op-grade op) ]ᶠ (curryᵐ k) ∘ᵖ η⊣ ⟩ᵐ)
            ≈ᵖ tickᵏ (op-grade op)
               ∘ᵖ [ mapᵉ (op-grade op) ]ᶠ
                   (implᵐ ∘ᵖ k
                    ∘ᵖ ⟨ idᵖ , op-semᵐ op ∘ᵖ ⟨ mapᵉ (op-grade op) ⟩ᶠ v ⟩ᵐ)
               ∘ᵖ η⊣
  implᵐ-opᵀ op v k z =
    tick-≈ (λ q → implˢ-cong
      (app-cong k
        ( transport-refl (⟨ mapᵉ (op-grade op) ⟩ᵒ _) (mk⟨⟩ q z)
        , ≈-refl ⟦ arity op ⟧ᵍ )))
