-------------------------------------------------------------------
-- Soundness of skeleton unification                             --
--                                                               --
-- A successful run of `unifyᵏ` returns a store whose denotation --
-- makes both sides of every equation it was given equal. The    --
-- proof mirrors the unifier, along the store extension `_++ᴷ_`, --
-- which acts on equations through `mono++ᵏ`.                    --
--                                                               --
-- Follows McBride's structural unification (JFP 2003).          --
-------------------------------------------------------------------

open import Data.Bool.Base using (if_then_else_)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′; _>>=_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Core.SkelUnifySound (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (_≡ᵇ?_)

open import TypeInference.SolverImpl.Core.Thick
open import TypeInference.SolverImpl.Core.Rigid     S using (zip₂; zip₂-just)
open import TypeInference.SolverImpl.Core.Skel      S
open import TypeInference.SolverImpl.Core.SkelUnify S

bind-just : ∀ {X Y : Set} → (m : Maybe X) → (f : X → Maybe Y) → {y : Y}
          → (m >>= f) ≡ just y → Σ[ x ∈ X ] ((m ≡ just x) × (f x ≡ just y))
bind-just (just x) f q = x , refl , q

-- The shape of the constant and variable comparisons

dec-if : ∀ {P X : Set} → (d : Dec P) → (m m' : Maybe X) → {y : X}
       → (if ⌊ d ⌋ then m else m') ≡ just y → (P × (m ≡ just y)) ⊎ (m' ≡ just y)
dec-if (yes r) m m' q = inj₁ (r , q)
dec-if (no  _) m m' q = inj₂ q

-- A skeleton that passes the occurrence check is left unchanged by
-- every binding of the checked variable.

checkᵏ-forᵏ : ∀ {n} → (α : Fin (suc n)) → (t : Skel (suc n)) → {u : Skel n}
            → checkᵏ α t ≡ just u → (s : Skel n) → t [ s forᵏ α ]ᵏ ≡ u
checkᵏ-forᵏ α (svar β)   q    s with map-just svar (thick α β) q
... | β₀ , r , refl = cong (maybe′ svar s) r
checkᵏ-forᵏ α (sBase b)  refl s = refl
checkᵏ-forᵏ α sUnit      refl s = refl
checkᵏ-forᵏ α sBool      refl s = refl
checkᵏ-forᵏ α sNat       refl s = refl
checkᵏ-forᵏ α (t₁ s× t₂) q    s with zip₂-just _s×_ (checkᵏ α t₁) (checkᵏ α t₂) q
... | _ , _ , q₁ , q₂ , refl =
  cong₂ _s×_ (checkᵏ-forᵏ α t₁ q₁ s) (checkᵏ-forᵏ α t₂ q₂ s)
checkᵏ-forᵏ α (t₁ s+ t₂) q    s with zip₂-just _s+_ (checkᵏ α t₁) (checkᵏ α t₂) q
... | _ , _ , q₁ , q₂ , refl =
  cong₂ _s+_ (checkᵏ-forᵏ α t₁ q₁ s) (checkᵏ-forᵏ α t₂ q₂ s)
checkᵏ-forᵏ α sEmpty     refl s = refl
checkᵏ-forᵏ α (t₁ s⇒ t₂) q    s with zip₂-just _s⇒_ (checkᵏ α t₁) (checkᵏ α t₂) q
... | _ , _ , q₁ , q₂ , refl =
  cong₂ _s⇒_ (checkᵏ-forᵏ α t₁ q₁ s) (checkᵏ-forᵏ α t₂ q₂ s)
checkᵏ-forᵏ α (sBox t₁)  q    s with map-just sBox_ (checkᵏ α t₁) q
... | _ , q₁ , refl = cong sBox_ (checkᵏ-forᵏ α t₁ q₁ s)
checkᵏ-forᵏ α (sList t₁) q    s with map-just sList (checkᵏ α t₁) q
... | _ , q₁ , refl = cong sList (checkᵏ-forᵏ α t₁ q₁ s)

anil-++ᴷ : ∀ {n m} → (τ : SAList n m) → anilᵏ ++ᴷ τ ≡ τ
anil-++ᴷ anilᵏ        = refl
anil-++ᴷ (t /ᵏ α ∷ τ) = cong (t /ᵏ α ∷_) (anil-++ᴷ τ)

++ᴷ-assoc : ∀ {n m l k} → (τ₃ : SAList l k) → (τ₂ : SAList m l) → (τ₁ : SAList n m)
          → (τ₃ ++ᴷ τ₂) ++ᴷ τ₁ ≡ τ₃ ++ᴷ (τ₂ ++ᴷ τ₁)
++ᴷ-assoc τ₃ τ₂ anilᵏ         = refl
++ᴷ-assoc τ₃ τ₂ (t /ᵏ α ∷ τ₁) = cong (t /ᵏ α ∷_) (++ᴷ-assoc τ₃ τ₂ τ₁)

-- An equation solved by a store is solved by every extension of it

mono++ᵏ : ∀ {n m l} → (τ : SAList n m) → (τ⁺ : SAList m l) → (e : SEqn n)
        → Unifies¹ᵏ e ⟦ τ ⟧ᴷ → Unifies¹ᵏ e ⟦ τ⁺ ++ᴷ τ ⟧ᴷ
mono++ᵏ τ τ⁺ (t , u) p =
  trans ([≐]ᵏ (⟦++⟧ᴷ τ⁺ τ) t)
        (trans (sym ([⨟]ᵏ t ⟦ τ ⟧ᴷ ⟦ τ⁺ ⟧ᴷ))
               (trans (cong (_[ ⟦ τ⁺ ⟧ᴷ ]ᵏ) p)
                      (trans ([⨟]ᵏ u ⟦ τ ⟧ᴷ ⟦ τ⁺ ⟧ᴷ)
                             (sym ([≐]ᵏ (⟦++⟧ᴷ τ⁺ τ) u)))))

-- Substituting into an equation before solving it

Unifies¹ᵏ-[]ᵏ : ∀ {n m l} → (t u : Skel n) → (σ : SSub n m) → (δ : SSub m l)
              → Unifies¹ᵏ (t [ σ ]ᵏ , u [ σ ]ᵏ) δ → Unifies¹ᵏ (t , u) (σ ⨟ᵏ δ)
Unifies¹ᵏ-[]ᵏ t u σ δ p = trans (sym ([⨟]ᵏ t σ δ)) (trans p ([⨟]ᵏ u σ δ))

-- The returned store extends the given one and solves the equation;
-- the equation is an index of the record type.

record Soundᵏ {n m l : ℕ} (e : SEqn n) (τ : SAList n m) (τ'' : SAList n l) : Set where
  constructor soundᵏ
  field
    ext  : SAList m l
    ext≡ : τ'' ≡ ext ++ᴷ τ
    sat  : Unifies¹ᵏ e ⟦ τ'' ⟧ᴷ

open Soundᵏ public

Soundᵏ-map : ∀ {n m l} {e e' : SEqn n} {τ : SAList n m} {τ'' : SAList n l}
           → (Unifies¹ᵏ e ⟦ τ'' ⟧ᴷ → Unifies¹ᵏ e' ⟦ τ'' ⟧ᴷ)
           → Soundᵏ e τ τ'' → Soundᵏ e' τ τ''
Soundᵏ-map f (soundᵏ τ⁺ r p) = soundᵏ τ⁺ r (f p)

-- Descending through one binding of the store

descᵏ : ∀ {n m l} → (t u : Skel (suc n)) → (r : Skel n) → (α : Fin (suc n))
      → (τ : SAList n m) → (τ' : SAList n l)
      → Soundᵏ (t [ r forᵏ α ]ᵏ , u [ r forᵏ α ]ᵏ) τ τ'
      → Soundᵏ (t , u) (r /ᵏ α ∷ τ) (r /ᵏ α ∷ τ')
descᵏ t u r α τ τ' (soundᵏ τ⁺ p q) =
  soundᵏ τ⁺ (cong (r /ᵏ α ∷_) p) (Unifies¹ᵏ-[]ᵏ t u (r forᵏ α) ⟦ τ' ⟧ᴷ q)

-- Two calls in sequence: the extensions compose, and the equation of
-- the first call is transported along the extension of the second

seq-soundᵏ : ∀ {n m l} {t₁ u₁ t₂ u₂ t u : Skel n}
               {τ : SAList n m} {τ'' : SAList n l}
           → (x : Maybe (Solᵏ n)) → (f : Solᵏ n → Maybe (Solᵏ n))
           → (∀ {m₁} → {τ₁ : SAList n m₁} → x ≡ just (m₁ , τ₁) → Soundᵏ (t₁ , u₁) τ τ₁)
           → (∀ {m₁ m₂} → (τ₁ : SAList n m₁) → {τ₂ : SAList n m₂}
                → f (m₁ , τ₁) ≡ just (m₂ , τ₂) → Soundᵏ (t₂ , u₂) τ₁ τ₂)
           → (Unifies¹ᵏ (t₁ , u₁) ⟦ τ'' ⟧ᴷ → Unifies¹ᵏ (t₂ , u₂) ⟦ τ'' ⟧ᴷ
                → Unifies¹ᵏ (t , u) ⟦ τ'' ⟧ᴷ)
           → (x >>= f) ≡ just (l , τ'') → Soundᵏ (t , u) τ τ''
seq-soundᵏ {t₁ = t₁} {u₁ = u₁} {τ = τ} x f s₁ s₂ cg eq with bind-just x f eq
... | (m₁ , τ₁) , q₁ , q₂ with s₁ q₁ | s₂ τ₁ q₂
...   | soundᵏ τ⁺₁ r₁ p₁ | soundᵏ τ⁺₂ r₂ p₂ =
        soundᵏ (τ⁺₂ ++ᴷ τ⁺₁)
               (trans r₂ (trans (cong (τ⁺₂ ++ᴷ_) r₁) (sym (++ᴷ-assoc τ⁺₂ τ⁺₁ τ))))
               (cg (subst (λ z → Unifies¹ᵏ (t₁ , u₁) ⟦ z ⟧ᴷ) (sym r₂)
                          (mono++ᵏ τ₁ τ⁺₂ (t₁ , u₁) p₁))
                   p₂)

-- Binding a variable, and the two-variable case

flexᵏ-sound : ∀ {n} → (α : Fin n) → (t : Skel n) → {m : ℕ} → {τ : SAList n m}
            → flexᵏ α t ≡ just (m , τ) → Soundᵏ (svar α , t) anilᵏ τ
flexᵏ-sound {zero}  ()
flexᵏ-sound {suc n} α t eq
  with map-just (λ u → n , u /ᵏ α ∷ anilᵏ) (checkᵏ α t) eq
... | u , q , refl = soundᵏ (u /ᵏ α ∷ anilᵏ) refl
                (begin
                   (u forᵏ α) α [ idᵏ ]ᵏ
                 ≡⟨ cong (_[ idᵏ ]ᵏ) (for-hitᵏ u α) ⟩
                   u [ idᵏ ]ᵏ
                 ≡⟨ [id]ᵏ u ⟩
                   u
                 ≡⟨ sym (checkᵏ-forᵏ α t q u) ⟩
                   t [ u forᵏ α ]ᵏ
                 ≡⟨ sym ([id]ᵏ (t [ u forᵏ α ]ᵏ)) ⟩
                   t [ u forᵏ α ]ᵏ [ idᵏ ]ᵏ
                 ≡⟨ [⨟]ᵏ t (u forᵏ α) idᵏ ⟩
                   t [ (u forᵏ α) ⨟ᵏ idᵏ ]ᵏ
                 ∎)

flexFlexᵏ-sound : ∀ {n} → (α β : Fin n) → {m : ℕ} → {τ : SAList n m}
                → flexFlexᵏ α β ≡ just (m , τ) → Soundᵏ (svar α , svar β) anilᵏ τ
flexFlexᵏ-sound {n} α β eq
  with dec-if (α ≟ᶠ β) (just (n , anilᵏ)) (flexᵏ α (svar β)) eq
... | inj₁ (r , refl) = soundᵏ anilᵏ refl (cong svar r)
... | inj₂ q          = flexᵏ-sound α (svar β) q

amguᵏ-sound : ∀ {n} → (t u : Skel n) → {m l : ℕ} → (τ : SAList n m)
            → {τ'' : SAList n l}
            → amguᵏ t u (m , τ) ≡ just (l , τ'') → Soundᵏ (t , u) τ τ''

amguᵏ-sound t u {m} (r /ᵏ α ∷ τ) eq
  with map-just (consᵏ r α)
                (amguᵏ (t [ r forᵏ α ]ᵏ) (u [ r forᵏ α ]ᵏ) (m , τ)) eq
... | (_ , τ') , q , refl =
  descᵏ t u r α τ τ' (amguᵏ-sound (t [ r forᵏ α ]ᵏ) (u [ r forᵏ α ]ᵏ) τ q)

amguᵏ-sound (svar α)   (svar β)   anilᵏ eq = flexFlexᵏ-sound α β eq
amguᵏ-sound (svar α)   (sBase b') anilᵏ eq = flexᵏ-sound α (sBase b') eq
amguᵏ-sound (svar α)   sUnit      anilᵏ eq = flexᵏ-sound α sUnit eq
amguᵏ-sound (svar α)   sBool      anilᵏ eq = flexᵏ-sound α sBool eq
amguᵏ-sound (svar α)   sNat       anilᵏ eq = flexᵏ-sound α sNat eq
amguᵏ-sound (svar α) (u₁ s× u₂)   anilᵏ eq = flexᵏ-sound α (u₁ s× u₂) eq
amguᵏ-sound (svar α) (u₁ s+ u₂)   anilᵏ eq = flexᵏ-sound α (u₁ s+ u₂) eq
amguᵏ-sound (svar α)   sEmpty     anilᵏ eq = flexᵏ-sound α sEmpty eq
amguᵏ-sound (svar α) (u₁ s⇒ u₂)   anilᵏ eq = flexᵏ-sound α (u₁ s⇒ u₂) eq
amguᵏ-sound (svar α)  (sBox u₁)   anilᵏ eq = flexᵏ-sound α (sBox u₁) eq
amguᵏ-sound (svar α)  (sList u₁)   anilᵏ eq = flexᵏ-sound α (sList u₁) eq

amguᵏ-sound (sBase b)   (svar β) anilᵏ eq = Soundᵏ-map sym (flexᵏ-sound β (sBase b) eq)
amguᵏ-sound sUnit       (svar β) anilᵏ eq = Soundᵏ-map sym (flexᵏ-sound β sUnit eq)
amguᵏ-sound sBool       (svar β) anilᵏ eq = Soundᵏ-map sym (flexᵏ-sound β sBool eq)
amguᵏ-sound sNat        (svar β) anilᵏ eq = Soundᵏ-map sym (flexᵏ-sound β sNat eq)
amguᵏ-sound (t₁ s× t₂)  (svar β) anilᵏ eq = Soundᵏ-map sym (flexᵏ-sound β (t₁ s× t₂) eq)
amguᵏ-sound (t₁ s+ t₂)  (svar β) anilᵏ eq = Soundᵏ-map sym (flexᵏ-sound β (t₁ s+ t₂) eq)
amguᵏ-sound sEmpty      (svar β) anilᵏ eq = Soundᵏ-map sym (flexᵏ-sound β sEmpty eq)
amguᵏ-sound (t₁ s⇒ t₂)  (svar β) anilᵏ eq = Soundᵏ-map sym (flexᵏ-sound β (t₁ s⇒ t₂) eq)
amguᵏ-sound (sBox t₁)   (svar β) anilᵏ eq = Soundᵏ-map sym (flexᵏ-sound β (sBox t₁) eq)
amguᵏ-sound (sList t₁)   (svar β) anilᵏ eq = Soundᵏ-map sym (flexᵏ-sound β (sList t₁) eq)

amguᵏ-sound {n} (sBase b) (sBase b') anilᵏ eq
  with dec-if (b ≡ᵇ? b') (just (n , anilᵏ)) nothing eq
... | inj₁ (r , refl) = soundᵏ anilᵏ refl (cong sBase r)
... | inj₂ ()
amguᵏ-sound (sBase b) sUnit        anilᵏ ()
amguᵏ-sound (sBase b) sBool        anilᵏ ()
amguᵏ-sound (sBase b) sNat         anilᵏ ()
amguᵏ-sound (sBase b) (u₁ s× u₂)   anilᵏ ()
amguᵏ-sound (sBase b) (u₁ s+ u₂)   anilᵏ ()
amguᵏ-sound (sBase b) sEmpty       anilᵏ ()
amguᵏ-sound (sBase b) (u₁ s⇒ u₂)   anilᵏ ()
amguᵏ-sound (sBase b) (sBox u₁)    anilᵏ ()
amguᵏ-sound (sBase b) (sList u₁)    anilᵏ ()

amguᵏ-sound sUnit (sBase b')       anilᵏ ()
amguᵏ-sound sUnit sUnit            anilᵏ refl = soundᵏ anilᵏ refl refl
amguᵏ-sound sUnit sBool            anilᵏ ()
amguᵏ-sound sUnit sNat             anilᵏ ()
amguᵏ-sound sUnit (u₁ s× u₂)       anilᵏ ()
amguᵏ-sound sUnit (u₁ s+ u₂)       anilᵏ ()
amguᵏ-sound sUnit sEmpty           anilᵏ ()
amguᵏ-sound sUnit (u₁ s⇒ u₂)       anilᵏ ()
amguᵏ-sound sUnit (sBox u₁)        anilᵏ ()
amguᵏ-sound sUnit (sList u₁)        anilᵏ ()

amguᵏ-sound sBool (sBase b')       anilᵏ ()
amguᵏ-sound sBool sUnit            anilᵏ ()
amguᵏ-sound sBool sBool            anilᵏ refl = soundᵏ anilᵏ refl refl
amguᵏ-sound sBool sNat             anilᵏ ()
amguᵏ-sound sBool (u₁ s× u₂)       anilᵏ ()
amguᵏ-sound sBool (u₁ s+ u₂)       anilᵏ ()
amguᵏ-sound sBool sEmpty           anilᵏ ()
amguᵏ-sound sBool (u₁ s⇒ u₂)       anilᵏ ()
amguᵏ-sound sBool (sBox u₁)        anilᵏ ()
amguᵏ-sound sBool (sList u₁)        anilᵏ ()
amguᵏ-sound sNat (sBase b')       anilᵏ ()
amguᵏ-sound sNat sUnit            anilᵏ ()
amguᵏ-sound sNat sBool            anilᵏ ()
amguᵏ-sound sNat sNat             anilᵏ refl = soundᵏ anilᵏ refl refl
amguᵏ-sound sNat (u₁ s× u₂)       anilᵏ ()
amguᵏ-sound sNat (u₁ s+ u₂)       anilᵏ ()
amguᵏ-sound sNat sEmpty           anilᵏ ()
amguᵏ-sound sNat (u₁ s⇒ u₂)       anilᵏ ()
amguᵏ-sound sNat (sBox u₁)        anilᵏ ()
amguᵏ-sound sNat (sList u₁)        anilᵏ ()

amguᵏ-sound (t₁ s× t₂) (sBase b')  anilᵏ ()
amguᵏ-sound (t₁ s× t₂) sUnit       anilᵏ ()
amguᵏ-sound (t₁ s× t₂) sBool       anilᵏ ()
amguᵏ-sound (t₁ s× t₂) sNat        anilᵏ ()
amguᵏ-sound {n} (t₁ s× t₂) (u₁ s× u₂) anilᵏ eq =
  seq-soundᵏ (amguᵏ t₁ u₁ (n , anilᵏ)) (amguᵏ t₂ u₂)
             (amguᵏ-sound t₁ u₁ anilᵏ) (amguᵏ-sound t₂ u₂)
             (cong₂ _s×_) eq
amguᵏ-sound (t₁ s× t₂) (u₁ s+ u₂)  anilᵏ ()
amguᵏ-sound (t₁ s× t₂) sEmpty      anilᵏ ()
amguᵏ-sound (t₁ s× t₂) (u₁ s⇒ u₂)  anilᵏ ()
amguᵏ-sound (t₁ s× t₂) (sBox u₁)   anilᵏ ()
amguᵏ-sound (t₁ s× t₂) (sList u₁)   anilᵏ ()
amguᵏ-sound (t₁ s+ t₂) (sBase b')  anilᵏ ()
amguᵏ-sound (t₁ s+ t₂) sUnit       anilᵏ ()
amguᵏ-sound (t₁ s+ t₂) sBool       anilᵏ ()
amguᵏ-sound (t₁ s+ t₂) sNat        anilᵏ ()
amguᵏ-sound {n} (t₁ s+ t₂) (u₁ s+ u₂) anilᵏ eq =
  seq-soundᵏ (amguᵏ t₁ u₁ (n , anilᵏ)) (amguᵏ t₂ u₂)
             (amguᵏ-sound t₁ u₁ anilᵏ) (amguᵏ-sound t₂ u₂)
             (cong₂ _s+_) eq
amguᵏ-sound (t₁ s+ t₂) (u₁ s× u₂)  anilᵏ ()
amguᵏ-sound (t₁ s+ t₂) sEmpty      anilᵏ ()
amguᵏ-sound (t₁ s+ t₂) (u₁ s⇒ u₂)  anilᵏ ()
amguᵏ-sound (t₁ s+ t₂) (sBox u₁)   anilᵏ ()
amguᵏ-sound (t₁ s+ t₂) (sList u₁)   anilᵏ ()

amguᵏ-sound sEmpty (sBase b')      anilᵏ ()
amguᵏ-sound sEmpty sUnit           anilᵏ ()
amguᵏ-sound sEmpty sBool           anilᵏ ()
amguᵏ-sound sEmpty sNat            anilᵏ ()
amguᵏ-sound sEmpty (u₁ s× u₂)      anilᵏ ()
amguᵏ-sound sEmpty (u₁ s+ u₂)      anilᵏ ()
amguᵏ-sound sEmpty sEmpty          anilᵏ refl = soundᵏ anilᵏ refl refl
amguᵏ-sound sEmpty (u₁ s⇒ u₂)      anilᵏ ()
amguᵏ-sound sEmpty (sBox u₁)       anilᵏ ()
amguᵏ-sound sEmpty (sList u₁)       anilᵏ ()

amguᵏ-sound (t₁ s⇒ t₂) (sBase b')  anilᵏ ()
amguᵏ-sound (t₁ s⇒ t₂) sUnit       anilᵏ ()
amguᵏ-sound (t₁ s⇒ t₂) sBool       anilᵏ ()
amguᵏ-sound (t₁ s⇒ t₂) sNat        anilᵏ ()
amguᵏ-sound (t₁ s⇒ t₂) (u₁ s× u₂)  anilᵏ ()
amguᵏ-sound (t₁ s⇒ t₂) (u₁ s+ u₂)  anilᵏ ()
amguᵏ-sound (t₁ s⇒ t₂) sEmpty      anilᵏ ()
amguᵏ-sound {n} (t₁ s⇒ t₂) (u₁ s⇒ u₂) anilᵏ eq =
  seq-soundᵏ (amguᵏ t₁ u₁ (n , anilᵏ)) (amguᵏ t₂ u₂)
             (amguᵏ-sound t₁ u₁ anilᵏ) (amguᵏ-sound t₂ u₂)
             (cong₂ _s⇒_) eq
amguᵏ-sound (t₁ s⇒ t₂) (sBox u₁)   anilᵏ ()
amguᵏ-sound (t₁ s⇒ t₂) (sList u₁)   anilᵏ ()

amguᵏ-sound (sBox t₁) (sBase b')   anilᵏ ()
amguᵏ-sound (sBox t₁) sUnit        anilᵏ ()
amguᵏ-sound (sBox t₁) sBool        anilᵏ ()
amguᵏ-sound (sBox t₁) sNat         anilᵏ ()
amguᵏ-sound (sBox t₁) (u₁ s× u₂)   anilᵏ ()
amguᵏ-sound (sBox t₁) (u₁ s+ u₂)   anilᵏ ()
amguᵏ-sound (sBox t₁) sEmpty       anilᵏ ()
amguᵏ-sound (sBox t₁) (u₁ s⇒ u₂)   anilᵏ ()
amguᵏ-sound (sBox t₁) (sBox u₁)    anilᵏ eq =
  Soundᵏ-map (cong sBox_) (amguᵏ-sound t₁ u₁ anilᵏ eq)
amguᵏ-sound (sBox t₁) (sList u₁)   anilᵏ ()

amguᵏ-sound (sList t₁) (sBase b')  anilᵏ ()
amguᵏ-sound (sList t₁) sUnit       anilᵏ ()
amguᵏ-sound (sList t₁) sBool       anilᵏ ()
amguᵏ-sound (sList t₁) sNat        anilᵏ ()
amguᵏ-sound (sList t₁) (u₁ s× u₂)  anilᵏ ()
amguᵏ-sound (sList t₁) (u₁ s+ u₂)  anilᵏ ()
amguᵏ-sound (sList t₁) sEmpty      anilᵏ ()
amguᵏ-sound (sList t₁) (u₁ s⇒ u₂)  anilᵏ ()
amguᵏ-sound (sList t₁) (sBox u₁)   anilᵏ ()
amguᵏ-sound (sList t₁) (sList u₁)  anilᵏ eq =
  Soundᵏ-map (cong sList) (amguᵏ-sound t₁ u₁ anilᵏ eq)

unifyᴷ-sound : ∀ {n} → (es : SEqns n) → {m l : ℕ} → (τ : SAList n m)
             → {τ'' : SAList n l}
             → unifyᴷ es (m , τ) ≡ just (l , τ'')
             → Σ[ τ⁺ ∈ SAList m l ] ((τ'' ≡ τ⁺ ++ᴷ τ) × Unifiesᵏ es ⟦ τ'' ⟧ᴷ)
unifyᴷ-sound []             τ refl = anilᵏ , sym (anil-++ᴷ τ) , tt
unifyᴷ-sound ((t , u) ∷ es) {m} τ eq
  with bind-just (amguᵏ t u (m , τ)) (unifyᴷ es) eq
... | (m₁ , τ₁) , q₁ , q₂ with amguᵏ-sound t u τ q₁ | unifyᴷ-sound es τ₁ q₂
...   | soundᵏ τ⁺₁ r₁ p₁ | τ⁺₂ , r₂ , ps =
        τ⁺₂ ++ᴷ τ⁺₁ ,
        trans r₂ (trans (cong (τ⁺₂ ++ᴷ_) r₁) (sym (++ᴷ-assoc τ⁺₂ τ⁺₁ τ))) ,
        (subst (λ z → Unifies¹ᵏ (t , u) ⟦ z ⟧ᴷ) (sym r₂)
               (mono++ᵏ τ₁ τ⁺₂ (t , u) p₁) , ps)

unifyᵏ-sound : ∀ {n m} → (es : SEqns n) → {τ : SAList n m}
             → unifyᵏ es ≡ just (m , τ) → Unifiesᵏ es ⟦ τ ⟧ᴷ
unifyᵏ-sound es eq with unifyᴷ-sound es anilᵏ eq
... | _ , _ , ps = ps
