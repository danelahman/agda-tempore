------------------------------------------------------------------
-- Soundness of unification                                      --
--                                                               --
-- A successful run of `unify` returns a store whose denotation   --
-- makes both sides of every equation it was given equal. The     --
-- proof mirrors the unifier: each successful `amgu*` call is     --
-- shown to return a store that extends the one it was given,     --
-- and to satisfy its own equation under the returned store.      --
-- Equations solved earlier are transported along the extensions  --
-- of the calls that follow.                                      --
--                                                               --
-- The extension is `_++ᴬ_` on stores: it is definitional for the --
-- store-descent clauses, composes by associativity, and acts on  --
-- equations through `mono++`.                                    --
--                                                               --
-- A clause of `amgu*` computes only once both the size index and --
-- the store are constructors, so each syntactic case is written  --
-- twice, once for each shape of the index.                       --
------------------------------------------------------------------

open import Data.Bool.Base using (if_then_else_; _∨_; true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′; _>>=_; _<∣>_)
  renaming (map to mmap)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import Inference.Scopes

module Inference.SolverImpl.Core.UnifySound (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (_≡ᵇ?_)

open import Inference.Open.Grades S
open import Inference.Open.Types  S
open import Inference.Open.Subst  S

open import Inference.SolverImpl.Core.Thick
open import Inference.SolverImpl.Core.For    S
open import Inference.SolverImpl.Core.AList  S
open import Inference.SolverImpl.Core.Eqn    S
open import Inference.SolverImpl.Core.Occurs S
open import Inference.SolverImpl.Core.Size   S
open import Inference.SolverImpl.Core.Unify  S

--------------------------------------------------------------
-- Inverting the combinators the unifier is built from       --
--------------------------------------------------------------

bind-just : ∀ {X Y : Set} → (m : Maybe X) → (f : X → Maybe Y) → {y : Y}
          → (m >>= f) ≡ just y → Σ[ x ∈ X ] ((m ≡ just x) × (f x ≡ just y))
bind-just (just x) f q = x , refl , q

alt-just : ∀ {X : Set} → (m m' : Maybe X) → {y : X}
         → (m <∣> m') ≡ just y → (m ≡ just y) ⊎ (m' ≡ just y)
alt-just (just x) m' refl = inj₁ refl
alt-just nothing  m' q    = inj₂ q

-- The shape of the occurrence checks

if-inv : ∀ {X : Set} → (b : 𝔹) → (x : X) → {y : X}
       → (if b then nothing else just x) ≡ just y → (b ≡ false) × (x ≡ y)
if-inv false x refl = refl , refl
if-inv true  x ()

-- The shape of the rigidity check

if-else : ∀ {X : Set} → (b : 𝔹) → (m : Maybe X) → {y : X}
        → (if b then nothing else m) ≡ just y → m ≡ just y
if-else false m q = q
if-else true  m ()

-- The shape of the constant and variable comparisons

dec-if : ∀ {P X : Set} → (d : Dec P) → (m m' : Maybe X) → {y : X}
       → (if ⌊ d ⌋ then m else m') ≡ just y → (P × (m ≡ just y)) ⊎ (m' ≡ just y)
dec-if (yes r) m m' q = inj₁ (r , q)
dec-if (no  _) m m' q = inj₂ q

dec-false : ∀ {P : Set} → (d : Dec P) → ⌊ d ⌋ ≡ false → ¬ P
dec-false (no nr) q = nr
dec-false (yes _) ()

∨-false : (b b' : 𝔹) → (b ∨ b') ≡ false → (b ≡ false) × (b' ≡ false)
∨-false false false q = refl , refl
∨-false false true  ()
∨-false true  b'    ()

--------------------------------------------------------------
-- A variable other than the eliminated one thickens         --
--------------------------------------------------------------

thick-¬ : ∀ {n} → (i j : Fin (suc n)) → ¬ (i ≡ j) → Σ[ k ∈ Fin n ] (thick i j ≡ just k)
thick-¬         zero    zero    ne = ⊥-elim (ne refl)
thick-¬         zero    (suc j) ne = j , refl
thick-¬ {suc n} (suc i) zero    ne = zero , refl
thick-¬ {suc n} (suc i) (suc j) ne with thick-¬ i j (λ r → ne (cong suc r))
... | k , q = suc k , cong (mmap suc) q

--------------------------------------------------------------
-- Grade expressions see only two of the three components    --
-- of a substitution                                         --
--------------------------------------------------------------

agreeᵉ : ∀ {Θ Θ'} {σ δ : Subst Θ Θ'} → ((i : EVar Θ) → sE σ i ≡ sE δ i)
       → (ε : EExp Θ) → ε [ σ ]ᵉ ≡ ε [ δ ]ᵉ
agreeᵉ q (evar i)   = q i
agreeᵉ q (econst c) = refl
agreeᵉ q (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ (agreeᵉ q ε) (agreeᵉ q ε')

agreeʳ : ∀ {Θ Θ'} {σ δ : Subst Θ Θ'} → ((i : RVar Θ) → sR σ i ≡ sR δ i)
       → ((i : EVar Θ) → sE σ i ≡ sE δ i) → (ρ : RExp Θ) → ρ [ σ ]ʳ ≡ ρ [ δ ]ʳ
agreeʳ qr qe (rvar i)   = qr i
agreeʳ qr qe (rconst c) = refl
agreeʳ qr qe (ρ ·̂ᵣ ρ')  = cong₂ _·̂ᵣ_ (agreeʳ qr qe ρ) (agreeʳ qr qe ρ')
agreeʳ qr qe ∣ ε ∣̂ᵉ     = cong ∣_∣̂ᵉ (agreeᵉ qe ε)

--------------------------------------------------------------
-- An expression the eliminated variable misses does not see --
-- the image it is eliminated to                             --
--------------------------------------------------------------

irrᵉ-e : ∀ {Θ} → (i : EVar (Θ +e)) → (X Y : EExp Θ) → (ε : EExp (Θ +e))
       → occᵉ-e i ε ≡ false → ε [ X forᵉ i ]ᵉ ≡ ε [ Y forᵉ i ]ᵉ
irrᵉ-e i X Y (evar j) q with thick-¬ i j (dec-false (i ≟ᶠ j) q)
... | j' , r = trans (cong (maybe′ evar X) r) (sym (cong (maybe′ evar Y) r))
irrᵉ-e i X Y (econst c) q = refl
irrᵉ-e i X Y (ε ·̂ₑ ε')  q with ∨-false (occᵉ-e i ε) (occᵉ-e i ε') q
... | q₁ , q₂ = cong₂ _·̂ₑ_ (irrᵉ-e i X Y ε q₁) (irrᵉ-e i X Y ε' q₂)

irrʳ-r : ∀ {Θ} → (i : RVar (Θ +r)) → (X Y : RExp Θ) → (ρ : RExp (Θ +r))
       → occʳ-r i ρ ≡ false → ρ [ X forʳ i ]ʳ ≡ ρ [ Y forʳ i ]ʳ
irrʳ-r i X Y (rvar j) q with thick-¬ i j (dec-false (i ≟ᶠ j) q)
... | j' , r = trans (cong (maybe′ rvar X) r) (sym (cong (maybe′ rvar Y) r))
irrʳ-r i X Y (rconst c) q = refl
irrʳ-r i X Y (ρ ·̂ᵣ ρ')  q with ∨-false (occʳ-r i ρ) (occʳ-r i ρ') q
... | q₁ , q₂ = cong₂ _·̂ᵣ_ (irrʳ-r i X Y ρ q₁) (irrʳ-r i X Y ρ' q₂)
irrʳ-r i X Y ∣ ε ∣̂ᵉ     q = cong ∣_∣̂ᵉ (agreeᵉ (λ j → refl) ε)

mutual

  irrᵗ-v : ∀ {Θ} → (α : TyVar (Θ +ty)) → (X Y : OVType Θ) → (A : OVType (Θ +ty))
         → occᵗ-v α A ≡ false → A [ X forᵗ α ]ᵛ ≡ A [ Y forᵗ α ]ᵛ
  irrᵗ-v α X Y (tvar β) q with thick-¬ α β (dec-false (α ≟ᶠ β) q)
  ... | β' , r = trans (cong (maybe′ tvar X) r) (sym (cong (maybe′ tvar Y) r))
  irrᵗ-v α X Y (Base b)  q = refl
  irrᵗ-v α X Y Unit      q = refl
  irrᵗ-v α X Y Bool      q = refl
  irrᵗ-v α X Y (A |×| B) q with ∨-false (occᵗ-v α A) (occᵗ-v α B) q
  ... | q₁ , q₂ = cong₂ _|×|_ (irrᵗ-v α X Y A q₁) (irrᵗ-v α X Y B q₂)
  irrᵗ-v α X Y Empty     q = refl
  irrᵗ-v α X Y (A ⇒ C)   q with ∨-false (occᵗ-v α A) (occᵗ-c α C) q
  ... | q₁ , q₂ = cong₂ _⇒_ (irrᵗ-v α X Y A q₁) (irrᵗ-c α X Y C q₂)
  irrᵗ-v α X Y ([ ρ ] A) q =
    cong₂ [_]_ (agreeʳ (λ i → refl) (λ i → refl) ρ) (irrᵗ-v α X Y A q)

  irrᵗ-c : ∀ {Θ} → (α : TyVar (Θ +ty)) → (X Y : OVType Θ) → (C : OCType (Θ +ty))
         → occᵗ-c α C ≡ false → C [ X forᵗ α ]ᶜ ≡ C [ Y forᵗ α ]ᶜ
  irrᵗ-c α X Y (A ‼ ε) q = cong₂ _‼_ (irrᵗ-v α X Y A q) (agreeᵉ (λ i → refl) ε)

--------------------------------------------------------------
-- The algebra of store composition                          --
--------------------------------------------------------------

anil-++ᴬ : ∀ {Θ Θ'} → (ρ : AList Θ Θ') → anil ++ᴬ ρ ≡ ρ
anil-++ᴬ anil         = refl
anil-++ᴬ (A /ᵗ α ∷ ρ) = cong (A /ᵗ α ∷_) (anil-++ᴬ ρ)
anil-++ᴬ (X /ʳ i ∷ ρ) = cong (X /ʳ i ∷_) (anil-++ᴬ ρ)
anil-++ᴬ (ε /ᵉ i ∷ ρ) = cong (ε /ᵉ i ∷_) (anil-++ᴬ ρ)

++ᴬ-assoc : ∀ {Θ Θ₁ Θ₂ Θ₃} → (ρ₃ : AList Θ₂ Θ₃) → (ρ₂ : AList Θ₁ Θ₂) → (ρ₁ : AList Θ Θ₁)
          → (ρ₃ ++ᴬ ρ₂) ++ᴬ ρ₁ ≡ ρ₃ ++ᴬ (ρ₂ ++ᴬ ρ₁)
++ᴬ-assoc ρ₃ ρ₂ anil          = refl
++ᴬ-assoc ρ₃ ρ₂ (A /ᵗ α ∷ ρ₁) = cong (A /ᵗ α ∷_) (++ᴬ-assoc ρ₃ ρ₂ ρ₁)
++ᴬ-assoc ρ₃ ρ₂ (X /ʳ i ∷ ρ₁) = cong (X /ʳ i ∷_) (++ᴬ-assoc ρ₃ ρ₂ ρ₁)
++ᴬ-assoc ρ₃ ρ₂ (ε /ᵉ i ∷ ρ₁) = cong (ε /ᵉ i ∷_) (++ᴬ-assoc ρ₃ ρ₂ ρ₁)

sym≐ˢ : ∀ {Θ Θ'} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ → δ ≐ˢ σ
sym≐ˢ q = mk≐ˢ (λ α → sym (≐ᵗ q α)) (λ i → sym (≐ʳ q i)) (λ i → sym (≐ᵉ q i))

-- An equation solved by a store is solved by every extension of it

mono++ : ∀ {Θ Θ' Θ''} {ρ : AList Θ Θ'} → (ρ⁺ : AList Θ' Θ'') → (e : Eqn Θ)
       → Unifies¹ e ⟦ ρ ⟧ᴬ → Unifies¹ e ⟦ ρ⁺ ++ᴬ ρ ⟧ᴬ
mono++ {ρ = ρ} ρ⁺ e u =
  Unifies¹-resp-≐ˢ (sym≐ˢ (⟦++⟧ᴬ ρ⁺ ρ)) e (Unifies¹-mono ⟦ ρ⁺ ⟧ᴬ e u)

-- Substituting into an equation before solving it

Unifies¹-[]ᴱ : ∀ {Θ Θ' Θ''} → (e : Eqn Θ) → (τ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
             → Unifies¹ (e [ τ ]ᴱ) δ → Unifies¹ e (τ ⨟ˢ δ)
Unifies¹-[]ᴱ (eqᵛ A B)  τ δ u = trans (sym ([⨟]ᵛ A τ δ)) (trans u ([⨟]ᵛ B τ δ))
Unifies¹-[]ᴱ (eqᶜ C D)  τ δ u = trans (sym ([⨟]ᶜ C τ δ)) (trans u ([⨟]ᶜ D τ δ))
Unifies¹-[]ᴱ (eqʳ ρ ρ') τ δ u = trans (sym ([⨟]ʳ ρ τ δ)) (trans u ([⨟]ʳ ρ' τ δ))
Unifies¹-[]ᴱ (eqᵉ ε ε') τ δ u = trans (sym ([⨟]ᵉ ε τ δ)) (trans u ([⨟]ᵉ ε' τ δ))

--------------------------------------------------------------
-- What one successful call establishes                      --
--------------------------------------------------------------

-- The returned store extends the given one, and solves the equation.
-- A record, so that the equation is recovered from the type.

record Sound {Θ Θ' Θ'' : Scope} (e : Eqn Θ) (ρ : AList Θ Θ') (ρ'' : AList Θ Θ'') : Set where
  constructor sound
  field
    ext  : AList Θ' Θ''
    ext≡ : ρ'' ≡ ext ++ᴬ ρ
    sat  : Unifies¹ e ⟦ ρ'' ⟧ᴬ

open Sound public

Sound-map : ∀ {Θ Θ' Θ''} {e e' : Eqn Θ} {ρ : AList Θ Θ'} {ρ'' : AList Θ Θ''}
          → (Unifies¹ e ⟦ ρ'' ⟧ᴬ → Unifies¹ e' ⟦ ρ'' ⟧ᴬ) → Sound e ρ ρ'' → Sound e' ρ ρ''
Sound-map f (sound ρ⁺ r u) = sound ρ⁺ r (f u)

-- Descending through one binding of the store

descᵗ : ∀ {Θ Θ' Θ''} → (e : Eqn (Θ +ty)) → (X : OVType Θ) → (α : TyVar (Θ +ty))
      → (τ : AList Θ Θ') → (τ' : AList Θ Θ'')
      → Sound (e [ X forᵗ α ]ᴱ) τ τ' → Sound e (X /ᵗ α ∷ τ) (X /ᵗ α ∷ τ')
descᵗ e X α τ τ' (sound ρ⁺ r u) =
  sound ρ⁺ (cong (X /ᵗ α ∷_) r) (Unifies¹-[]ᴱ e (X forᵗ α) ⟦ τ' ⟧ᴬ u)

descʳ : ∀ {Θ Θ' Θ''} → (e : Eqn (Θ +r)) → (X : RExp Θ) → (i : RVar (Θ +r))
      → (τ : AList Θ Θ') → (τ' : AList Θ Θ'')
      → Sound (e [ X forʳ i ]ᴱ) τ τ' → Sound e (X /ʳ i ∷ τ) (X /ʳ i ∷ τ')
descʳ e X i τ τ' (sound ρ⁺ r u) =
  sound ρ⁺ (cong (X /ʳ i ∷_) r) (Unifies¹-[]ᴱ e (X forʳ i) ⟦ τ' ⟧ᴬ u)

descᵉ : ∀ {Θ Θ' Θ''} → (e : Eqn (Θ +e)) → (X : EExp Θ) → (i : EVar (Θ +e))
      → (τ : AList Θ Θ') → (τ' : AList Θ Θ'')
      → Sound (e [ X forᵉ i ]ᴱ) τ τ' → Sound e (X /ᵉ i ∷ τ) (X /ᵉ i ∷ τ')
descᵉ e X i τ τ' (sound ρ⁺ r u) =
  sound ρ⁺ (cong (X /ᵉ i ∷_) r) (Unifies¹-[]ᴱ e (X forᵉ i) ⟦ τ' ⟧ᴬ u)

-- Two calls in sequence: the extensions compose, and the equation of
-- the first call is transported along the extension of the second

seq-sound : ∀ {Θ Θ' Θ''} {e₁ e₂ e : Eqn Θ} {ρ : AList Θ Θ'} {ρ'' : AList Θ Θ''}
          → (m : Maybe (Sol Θ)) → (f : Sol Θ → Maybe (Sol Θ))
          → (∀ {Θ₁} → {ρ₁ : AList Θ Θ₁} → m ≡ just (Θ₁ , ρ₁) → Sound e₁ ρ ρ₁)
          → (∀ {Θ₁ Θ₂} → (ρ₁ : AList Θ Θ₁) → {ρ₂ : AList Θ Θ₂}
               → f (Θ₁ , ρ₁) ≡ just (Θ₂ , ρ₂) → Sound e₂ ρ₁ ρ₂)
          → (Unifies¹ e₁ ⟦ ρ'' ⟧ᴬ → Unifies¹ e₂ ⟦ ρ'' ⟧ᴬ → Unifies¹ e ⟦ ρ'' ⟧ᴬ)
          → (m >>= f) ≡ just (Θ'' , ρ'') → Sound e ρ ρ''
seq-sound {e₁ = e₁} {ρ = ρ} m f s₁ s₂ cg eq with bind-just m f eq
... | (Θ₁ , ρ₁) , q₁ , q₂ with s₁ q₁ | s₂ ρ₁ q₂
...   | sound ρ⁺₁ r₁ u₁ | sound ρ⁺₂ r₂ u₂ =
        sound (ρ⁺₂ ++ᴬ ρ⁺₁)
              (trans r₂ (trans (cong (ρ⁺₂ ++ᴬ_) r₁) (sym (++ᴬ-assoc ρ⁺₂ ρ⁺₁ ρ))))
              (cg (subst (λ z → Unifies¹ e₁ ⟦ z ⟧ᴬ) (sym r₂) (mono++ ρ⁺₂ e₁ u₁)) u₂)

--------------------------------------------------------------
-- Binding a variable                                        --
--------------------------------------------------------------

flexᵗ-sound : ∀ {Θ} → (α : TyVar Θ) → (A : OVType Θ) → {Θ'' : Scope} → {ρ'' : AList Θ Θ''}
            → flexᵗ α A ≡ just (Θ'' , ρ'') → Sound (eqᵛ (tvar α) A) anil ρ''
flexᵗ-sound {scope (suc nt) nr ne} α A eq
  with map-just (λ A' → scope nt nr ne , A' /ᵗ α ∷ anil) (chkᵗ-v {scope nt nr ne} α A) eq
... | A' , q , refl with if-inv (occᵗ-v α A) (A [ Unit forᵗ α ]ᵛ) q
...   | o , r = sound (A' /ᵗ α ∷ anil) refl
                (begin
                   sTy (A' forᵗ α) α [ idˢ ]ᵛ
                 ≡⟨ cong (_[ idˢ ]ᵛ) (for-hitᵗ A' α) ⟩
                   A' [ idˢ ]ᵛ
                 ≡⟨ [id]ᵛ A' ⟩
                   A'
                 ≡⟨ sym r ⟩
                   A [ Unit forᵗ α ]ᵛ
                 ≡⟨ irrᵗ-v α Unit A' A o ⟩
                   A [ A' forᵗ α ]ᵛ
                 ≡⟨ sym ([id]ᵛ (A [ A' forᵗ α ]ᵛ)) ⟩
                   A [ A' forᵗ α ]ᵛ [ idˢ ]ᵛ
                 ≡⟨ [⨟]ᵛ A (A' forᵗ α) idˢ ⟩
                   A [ (A' forᵗ α) ⨟ˢ idˢ ]ᵛ
                 ∎)

flexʳ-sound : ∀ {Θ} → (i : RVar Θ) → (ρ : RExp Θ) → {Θ'' : Scope} → {ρ'' : AList Θ Θ''}
            → flexʳ i ρ ≡ just (Θ'' , ρ'') → Sound (eqʳ (rvar i) ρ) anil ρ''
flexʳ-sound {scope nt (suc nr) ne} i ρ eq
  with map-just (λ X → scope nt nr ne , X /ʳ i ∷ anil) (chkʳ-r {scope nt nr ne} i ρ) eq
... | X , q , refl with if-inv (occʳ-r i ρ) (ρ [ ûᵣ forʳ i ]ʳ) q
...   | o , r = sound (X /ʳ i ∷ anil) refl
                (begin
                   sR (X forʳ i) i [ idˢ ]ʳ
                 ≡⟨ cong (_[ idˢ ]ʳ) (for-hitʳ X i) ⟩
                   X [ idˢ ]ʳ
                 ≡⟨ [id]ʳ X ⟩
                   X
                 ≡⟨ sym r ⟩
                   ρ [ ûᵣ forʳ i ]ʳ
                 ≡⟨ irrʳ-r i ûᵣ X ρ o ⟩
                   ρ [ X forʳ i ]ʳ
                 ≡⟨ sym ([id]ʳ (ρ [ X forʳ i ]ʳ)) ⟩
                   ρ [ X forʳ i ]ʳ [ idˢ ]ʳ
                 ≡⟨ [⨟]ʳ ρ (X forʳ i) idˢ ⟩
                   ρ [ (X forʳ i) ⨟ˢ idˢ ]ʳ
                 ∎)

flexᵉ-sound : ∀ {Θ} → (rg : Rig Θ) → (i : EVar Θ) → (ε : EExp Θ)
            → {Θ'' : Scope} → {ρ'' : AList Θ Θ''}
            → flexᵉ rg i ε ≡ just (Θ'' , ρ'') → Sound (eqᵉ (evar i) ε) anil ρ''
flexᵉ-sound {scope nt nr (suc ne)} rg i ε eq
  with if-else (i ∈ᶠ rg)
               (mmap (λ X → scope nt nr ne , X /ᵉ i ∷ anil) (chkᵉ-e {scope nt nr ne} i ε)) eq
... | eq' with map-just (λ X → scope nt nr ne , X /ᵉ i ∷ anil) (chkᵉ-e {scope nt nr ne} i ε) eq'
... | X , q , refl with if-inv (occᵉ-e i ε) (ε [ ûₑ forᵉ i ]ᵉ) q
... | o , r = sound (X /ᵉ i ∷ anil) refl
                (begin
                   sE (X forᵉ i) i [ idˢ ]ᵉ
                 ≡⟨ cong (_[ idˢ ]ᵉ) (for-hitᵉ X i) ⟩
                   X [ idˢ ]ᵉ
                 ≡⟨ [id]ᵉ X ⟩
                   X
                 ≡⟨ sym r ⟩
                   ε [ ûₑ forᵉ i ]ᵉ
                 ≡⟨ irrᵉ-e i ûₑ X ε o ⟩
                   ε [ X forᵉ i ]ᵉ
                 ≡⟨ sym ([id]ᵉ (ε [ X forᵉ i ]ᵉ)) ⟩
                   ε [ X forᵉ i ]ᵉ [ idˢ ]ᵉ
                 ≡⟨ [⨟]ᵉ ε (X forᵉ i) idˢ ⟩
                   ε [ (X forᵉ i) ⨟ˢ idˢ ]ᵉ
                 ∎)

-- Two variables of the same sort

flexFlexᵗ-sound : ∀ {Θ} → (α β : TyVar Θ) → {Θ'' : Scope} → {ρ'' : AList Θ Θ''}
                → flexFlexᵗ α β ≡ just (Θ'' , ρ'') → Sound (eqᵛ (tvar α) (tvar β)) anil ρ''
flexFlexᵗ-sound {Θ} α β eq
  with dec-if (α ≟ᶠ β) (just (Θ , anil)) (flexᵗ α (tvar β)) eq
... | inj₁ (r , refl) = sound anil refl (cong tvar r)
... | inj₂ q          = flexᵗ-sound α (tvar β) q

flexFlexʳ-sound : ∀ {Θ} → (i j : RVar Θ) → {Θ'' : Scope} → {ρ'' : AList Θ Θ''}
                → flexFlexʳ i j ≡ just (Θ'' , ρ'') → Sound (eqʳ (rvar i) (rvar j)) anil ρ''
flexFlexʳ-sound {Θ} i j eq
  with dec-if (i ≟ᶠ j) (just (Θ , anil)) (flexʳ i (rvar j)) eq
... | inj₁ (r , refl) = sound anil refl (cong rvar r)
... | inj₂ q          = flexʳ-sound i (rvar j) q

flexFlexᵉ-sound : ∀ {Θ} → (rg : Rig Θ) → (i j : EVar Θ) → {Θ'' : Scope} → {ρ'' : AList Θ Θ''}
                → flexFlexᵉ rg i j ≡ just (Θ'' , ρ'') → Sound (eqᵉ (evar i) (evar j)) anil ρ''
flexFlexᵉ-sound {Θ} rg i j eq
  with dec-if (i ≟ᶠ j) (just (Θ , anil))
              (flexᵉ rg i (evar j) <∣> flexᵉ rg j (evar i)) eq
... | inj₁ (r , refl) = sound anil refl (cong evar r)
... | inj₂ q with alt-just (flexᵉ rg i (evar j)) (flexᵉ rg j (evar i)) q
...   | inj₁ q' = flexᵉ-sound rg i (evar j) q'
...   | inj₂ q' = Sound-map sym (flexᵉ-sound rg j (evar i) q')

--------------------------------------------------------------
-- Soundness of the unifier                                  --
--------------------------------------------------------------

mutual

  amguᵛ-sound : ∀ {Θ} → (k : ℕ) → (p : Sz Θ ≡ k) → (rg : Rig Θ) → (A B : OVType Θ)
              → {Θ' Θ'' : Scope} → (ρ : AList Θ Θ') → {ρ'' : AList Θ Θ''}
              → amguᵛ k p rg A B (Θ' , ρ) ≡ just (Θ'' , ρ'') → Sound (eqᵛ A B) ρ ρ''

  amguᶜ-sound : ∀ {Θ} → (k : ℕ) → (p : Sz Θ ≡ k) → (rg : Rig Θ) → (C D : OCType Θ)
              → {Θ' Θ'' : Scope} → (ρ : AList Θ Θ') → {ρ'' : AList Θ Θ''}
              → amguᶜ k p rg C D (Θ' , ρ) ≡ just (Θ'' , ρ'') → Sound (eqᶜ C D) ρ ρ''

  amguʳ-sound : ∀ {Θ} → (k : ℕ) → (p : Sz Θ ≡ k) → (rg : Rig Θ) → (ρ₀ ρ₁ : RExp Θ)
              → {Θ' Θ'' : Scope} → (ρ : AList Θ Θ') → {ρ'' : AList Θ Θ''}
              → amguʳ k p rg ρ₀ ρ₁ (Θ' , ρ) ≡ just (Θ'' , ρ'') → Sound (eqʳ ρ₀ ρ₁) ρ ρ''

  amguᵉ-sound : ∀ {Θ} → (k : ℕ) → (p : Sz Θ ≡ k) → (rg : Rig Θ) → (ε ε' : EExp Θ)
              → {Θ' Θ'' : Scope} → (ρ : AList Θ Θ') → {ρ'' : AList Θ Θ''}
              → amguᵉ k p rg ε ε' (Θ' , ρ) ≡ just (Θ'' , ρ'') → Sound (eqᵉ ε ε') ρ ρ''

  -- value types

  amguᵛ-sound (suc k) p rg A B {Θ'} (X /ᵗ α ∷ τ) eq
    with map-just (consᵗ X α)
                  (amguᵛ k (szᵗ τ p) rg (A [ X forᵗ α ]ᵛ) (B [ X forᵗ α ]ᵛ) (Θ' , τ)) eq
  ... | (Θ₂ , τ') , q , refl = descᵗ (eqᵛ A B) X α τ τ'
      (amguᵛ-sound k (szᵗ τ p) rg (A [ X forᵗ α ]ᵛ) (B [ X forᵗ α ]ᵛ) τ q)
  amguᵛ-sound (suc k) p rg A B {Θ'} (X /ʳ i ∷ τ) eq
    with map-just (consʳ X i)
                  (amguᵛ k (szʳ τ p) rg (A [ X forʳ i ]ᵛ) (B [ X forʳ i ]ᵛ) (Θ' , τ)) eq
  ... | (Θ₂ , τ') , q , refl = descʳ (eqᵛ A B) X i τ τ'
      (amguᵛ-sound k (szʳ τ p) rg (A [ X forʳ i ]ᵛ) (B [ X forʳ i ]ᵛ) τ q)
  amguᵛ-sound (suc k) p rg A B {Θ'} (X /ᵉ i ∷ τ) eq
    with map-just (consᵉ X i)
                  (amguᵛ k (szᵉ τ p) (popʳᵍ τ i rg) (A [ X forᵉ i ]ᵛ) (B [ X forᵉ i ]ᵛ) (Θ' , τ)) eq
  ... | (Θ₂ , τ') , q , refl = descᵉ (eqᵛ A B) X i τ τ'
      (amguᵛ-sound k (szᵉ τ p) (popʳᵍ τ i rg) (A [ X forᵉ i ]ᵛ) (B [ X forᵉ i ]ᵛ) τ q)
  amguᵛ-sound zero p rg A B (X /ᵗ α ∷ τ) eq = sz0ᵗ τ p
  amguᵛ-sound zero p rg A B (X /ʳ i ∷ τ) eq = sz0ʳ τ p
  amguᵛ-sound zero p rg A B (X /ᵉ i ∷ τ) eq = sz0ᵉ τ p

  amguᵛ-sound (suc k) p rg (tvar α) (tvar β) anil eq = flexFlexᵗ-sound α β eq
  amguᵛ-sound (suc k) p rg (tvar α) (Base b') anil eq = flexᵗ-sound α (Base b') eq
  amguᵛ-sound (suc k) p rg (tvar α) Unit anil eq = flexᵗ-sound α Unit eq
  amguᵛ-sound (suc k) p rg (tvar α) Bool anil eq = flexᵗ-sound α Bool eq
  amguᵛ-sound (suc k) p rg (tvar α) (B |×| B') anil eq = flexᵗ-sound α (B |×| B') eq
  amguᵛ-sound (suc k) p rg (tvar α) Empty anil eq = flexᵗ-sound α Empty eq
  amguᵛ-sound (suc k) p rg (tvar α) (B ⇒ D) anil eq = flexᵗ-sound α (B ⇒ D) eq
  amguᵛ-sound (suc k) p rg (tvar α) ([ ρ' ] B) anil eq = flexᵗ-sound α ([ ρ' ] B) eq
  amguᵛ-sound (suc k) p rg (Base b) (tvar β) anil eq = Sound-map sym (flexᵗ-sound β (Base b) eq)
  amguᵛ-sound (suc k) p rg Unit (tvar β) anil eq = Sound-map sym (flexᵗ-sound β Unit eq)
  amguᵛ-sound (suc k) p rg Bool (tvar β) anil eq = Sound-map sym (flexᵗ-sound β Bool eq)
  amguᵛ-sound (suc k) p rg (A |×| A') (tvar β) anil eq = Sound-map sym (flexᵗ-sound β (A |×| A') eq)
  amguᵛ-sound (suc k) p rg Empty (tvar β) anil eq = Sound-map sym (flexᵗ-sound β Empty eq)
  amguᵛ-sound (suc k) p rg (A ⇒ C) (tvar β) anil eq = Sound-map sym (flexᵗ-sound β (A ⇒ C) eq)
  amguᵛ-sound (suc k) p rg ([ ρ ] A) (tvar β) anil eq = Sound-map sym (flexᵗ-sound β ([ ρ ] A) eq)
  amguᵛ-sound {Θ} (suc k) p rg (Base b) (Base b') anil eq
    with dec-if (b ≡ᵇ? b') (just (Θ , anil)) nothing eq
  ... | inj₁ (r , refl) = sound anil refl (cong Base r)
  ... | inj₂ ()
  amguᵛ-sound (suc k) p rg (Base b) Unit anil ()
  amguᵛ-sound (suc k) p rg (Base b) Bool anil ()
  amguᵛ-sound (suc k) p rg (Base b) (B |×| B') anil ()
  amguᵛ-sound (suc k) p rg (Base b) Empty anil ()
  amguᵛ-sound (suc k) p rg (Base b) (B ⇒ D) anil ()
  amguᵛ-sound (suc k) p rg (Base b) ([ ρ' ] B) anil ()
  amguᵛ-sound (suc k) p rg Unit (Base b') anil ()
  amguᵛ-sound (suc k) p rg Unit Unit anil refl = sound anil refl refl
  amguᵛ-sound (suc k) p rg Unit Bool anil ()
  amguᵛ-sound (suc k) p rg Unit (B |×| B') anil ()
  amguᵛ-sound (suc k) p rg Unit Empty anil ()
  amguᵛ-sound (suc k) p rg Unit (B ⇒ D) anil ()
  amguᵛ-sound (suc k) p rg Unit ([ ρ' ] B) anil ()
  amguᵛ-sound (suc k) p rg Bool (Base b') anil ()
  amguᵛ-sound (suc k) p rg Bool Unit anil ()
  amguᵛ-sound (suc k) p rg Bool Bool anil refl = sound anil refl refl
  amguᵛ-sound (suc k) p rg Bool (B |×| B') anil ()
  amguᵛ-sound (suc k) p rg Bool Empty anil ()
  amguᵛ-sound (suc k) p rg Bool (B ⇒ D) anil ()
  amguᵛ-sound (suc k) p rg Bool ([ ρ' ] B) anil ()
  amguᵛ-sound (suc k) p rg (A |×| A') (Base b') anil ()
  amguᵛ-sound (suc k) p rg (A |×| A') Unit anil ()
  amguᵛ-sound (suc k) p rg (A |×| A') Bool anil ()
  amguᵛ-sound {Θ} (suc k) p rg (A |×| A') (B |×| B') anil eq =
    seq-sound (amguᵛ (suc k) p rg A B (Θ , anil)) (amguᵛ (suc k) p rg A' B')
              (amguᵛ-sound (suc k) p rg A B anil) (amguᵛ-sound (suc k) p rg A' B')
              (cong₂ _|×|_) eq
  amguᵛ-sound (suc k) p rg (A |×| A') Empty anil ()
  amguᵛ-sound (suc k) p rg (A |×| A') (B ⇒ D) anil ()
  amguᵛ-sound (suc k) p rg (A |×| A') ([ ρ' ] B) anil ()
  amguᵛ-sound (suc k) p rg Empty (Base b') anil ()
  amguᵛ-sound (suc k) p rg Empty Unit anil ()
  amguᵛ-sound (suc k) p rg Empty Bool anil ()
  amguᵛ-sound (suc k) p rg Empty (B |×| B') anil ()
  amguᵛ-sound (suc k) p rg Empty Empty anil refl = sound anil refl refl
  amguᵛ-sound (suc k) p rg Empty (B ⇒ D) anil ()
  amguᵛ-sound (suc k) p rg Empty ([ ρ' ] B) anil ()
  amguᵛ-sound (suc k) p rg (A ⇒ C) (Base b') anil ()
  amguᵛ-sound (suc k) p rg (A ⇒ C) Unit anil ()
  amguᵛ-sound (suc k) p rg (A ⇒ C) Bool anil ()
  amguᵛ-sound (suc k) p rg (A ⇒ C) (B |×| B') anil ()
  amguᵛ-sound (suc k) p rg (A ⇒ C) Empty anil ()
  amguᵛ-sound {Θ} (suc k) p rg (A ⇒ C) (B ⇒ D) anil eq =
    seq-sound (amguᵛ (suc k) p rg A B (Θ , anil)) (amguᶜ (suc k) p rg C D)
              (amguᵛ-sound (suc k) p rg A B anil) (amguᶜ-sound (suc k) p rg C D)
              (cong₂ _⇒_) eq
  amguᵛ-sound (suc k) p rg (A ⇒ C) ([ ρ' ] B) anil ()
  amguᵛ-sound (suc k) p rg ([ ρ ] A) (Base b') anil ()
  amguᵛ-sound (suc k) p rg ([ ρ ] A) Unit anil ()
  amguᵛ-sound (suc k) p rg ([ ρ ] A) Bool anil ()
  amguᵛ-sound (suc k) p rg ([ ρ ] A) (B |×| B') anil ()
  amguᵛ-sound (suc k) p rg ([ ρ ] A) Empty anil ()
  amguᵛ-sound (suc k) p rg ([ ρ ] A) (B ⇒ D) anil ()
  amguᵛ-sound {Θ} (suc k) p rg ([ ρ ] A) ([ ρ' ] B) anil eq =
    seq-sound (amguʳ (suc k) p rg ρ ρ' (Θ , anil)) (amguᵛ (suc k) p rg A B)
              (amguʳ-sound (suc k) p rg ρ ρ' anil) (amguᵛ-sound (suc k) p rg A B)
              (cong₂ [_]_) eq

  amguᵛ-sound zero p rg (tvar α) (tvar β) anil eq = flexFlexᵗ-sound α β eq
  amguᵛ-sound zero p rg (tvar α) (Base b') anil eq = flexᵗ-sound α (Base b') eq
  amguᵛ-sound zero p rg (tvar α) Unit anil eq = flexᵗ-sound α Unit eq
  amguᵛ-sound zero p rg (tvar α) Bool anil eq = flexᵗ-sound α Bool eq
  amguᵛ-sound zero p rg (tvar α) (B |×| B') anil eq = flexᵗ-sound α (B |×| B') eq
  amguᵛ-sound zero p rg (tvar α) Empty anil eq = flexᵗ-sound α Empty eq
  amguᵛ-sound zero p rg (tvar α) (B ⇒ D) anil eq = flexᵗ-sound α (B ⇒ D) eq
  amguᵛ-sound zero p rg (tvar α) ([ ρ' ] B) anil eq = flexᵗ-sound α ([ ρ' ] B) eq
  amguᵛ-sound zero p rg (Base b) (tvar β) anil eq = Sound-map sym (flexᵗ-sound β (Base b) eq)
  amguᵛ-sound zero p rg Unit (tvar β) anil eq = Sound-map sym (flexᵗ-sound β Unit eq)
  amguᵛ-sound zero p rg Bool (tvar β) anil eq = Sound-map sym (flexᵗ-sound β Bool eq)
  amguᵛ-sound zero p rg (A |×| A') (tvar β) anil eq = Sound-map sym (flexᵗ-sound β (A |×| A') eq)
  amguᵛ-sound zero p rg Empty (tvar β) anil eq = Sound-map sym (flexᵗ-sound β Empty eq)
  amguᵛ-sound zero p rg (A ⇒ C) (tvar β) anil eq = Sound-map sym (flexᵗ-sound β (A ⇒ C) eq)
  amguᵛ-sound zero p rg ([ ρ ] A) (tvar β) anil eq = Sound-map sym (flexᵗ-sound β ([ ρ ] A) eq)
  amguᵛ-sound {Θ} zero p rg (Base b) (Base b') anil eq
    with dec-if (b ≡ᵇ? b') (just (Θ , anil)) nothing eq
  ... | inj₁ (r , refl) = sound anil refl (cong Base r)
  ... | inj₂ ()
  amguᵛ-sound zero p rg (Base b) Unit anil ()
  amguᵛ-sound zero p rg (Base b) Bool anil ()
  amguᵛ-sound zero p rg (Base b) (B |×| B') anil ()
  amguᵛ-sound zero p rg (Base b) Empty anil ()
  amguᵛ-sound zero p rg (Base b) (B ⇒ D) anil ()
  amguᵛ-sound zero p rg (Base b) ([ ρ' ] B) anil ()
  amguᵛ-sound zero p rg Unit (Base b') anil ()
  amguᵛ-sound zero p rg Unit Unit anil refl = sound anil refl refl
  amguᵛ-sound zero p rg Unit Bool anil ()
  amguᵛ-sound zero p rg Unit (B |×| B') anil ()
  amguᵛ-sound zero p rg Unit Empty anil ()
  amguᵛ-sound zero p rg Unit (B ⇒ D) anil ()
  amguᵛ-sound zero p rg Unit ([ ρ' ] B) anil ()
  amguᵛ-sound zero p rg Bool (Base b') anil ()
  amguᵛ-sound zero p rg Bool Unit anil ()
  amguᵛ-sound zero p rg Bool Bool anil refl = sound anil refl refl
  amguᵛ-sound zero p rg Bool (B |×| B') anil ()
  amguᵛ-sound zero p rg Bool Empty anil ()
  amguᵛ-sound zero p rg Bool (B ⇒ D) anil ()
  amguᵛ-sound zero p rg Bool ([ ρ' ] B) anil ()
  amguᵛ-sound zero p rg (A |×| A') (Base b') anil ()
  amguᵛ-sound zero p rg (A |×| A') Unit anil ()
  amguᵛ-sound zero p rg (A |×| A') Bool anil ()
  amguᵛ-sound {Θ} zero p rg (A |×| A') (B |×| B') anil eq =
    seq-sound (amguᵛ zero p rg A B (Θ , anil)) (amguᵛ zero p rg A' B')
              (amguᵛ-sound zero p rg A B anil) (amguᵛ-sound zero p rg A' B')
              (cong₂ _|×|_) eq
  amguᵛ-sound zero p rg (A |×| A') Empty anil ()
  amguᵛ-sound zero p rg (A |×| A') (B ⇒ D) anil ()
  amguᵛ-sound zero p rg (A |×| A') ([ ρ' ] B) anil ()
  amguᵛ-sound zero p rg Empty (Base b') anil ()
  amguᵛ-sound zero p rg Empty Unit anil ()
  amguᵛ-sound zero p rg Empty Bool anil ()
  amguᵛ-sound zero p rg Empty (B |×| B') anil ()
  amguᵛ-sound zero p rg Empty Empty anil refl = sound anil refl refl
  amguᵛ-sound zero p rg Empty (B ⇒ D) anil ()
  amguᵛ-sound zero p rg Empty ([ ρ' ] B) anil ()
  amguᵛ-sound zero p rg (A ⇒ C) (Base b') anil ()
  amguᵛ-sound zero p rg (A ⇒ C) Unit anil ()
  amguᵛ-sound zero p rg (A ⇒ C) Bool anil ()
  amguᵛ-sound zero p rg (A ⇒ C) (B |×| B') anil ()
  amguᵛ-sound zero p rg (A ⇒ C) Empty anil ()
  amguᵛ-sound {Θ} zero p rg (A ⇒ C) (B ⇒ D) anil eq =
    seq-sound (amguᵛ zero p rg A B (Θ , anil)) (amguᶜ zero p rg C D)
              (amguᵛ-sound zero p rg A B anil) (amguᶜ-sound zero p rg C D)
              (cong₂ _⇒_) eq
  amguᵛ-sound zero p rg (A ⇒ C) ([ ρ' ] B) anil ()
  amguᵛ-sound zero p rg ([ ρ ] A) (Base b') anil ()
  amguᵛ-sound zero p rg ([ ρ ] A) Unit anil ()
  amguᵛ-sound zero p rg ([ ρ ] A) Bool anil ()
  amguᵛ-sound zero p rg ([ ρ ] A) (B |×| B') anil ()
  amguᵛ-sound zero p rg ([ ρ ] A) Empty anil ()
  amguᵛ-sound zero p rg ([ ρ ] A) (B ⇒ D) anil ()
  amguᵛ-sound {Θ} zero p rg ([ ρ ] A) ([ ρ' ] B) anil eq =
    seq-sound (amguʳ zero p rg ρ ρ' (Θ , anil)) (amguᵛ zero p rg A B)
              (amguʳ-sound zero p rg ρ ρ' anil) (amguᵛ-sound zero p rg A B)
              (cong₂ [_]_) eq

  -- computation types

  amguᶜ-sound (suc k) p rg C D {Θ'} (X /ᵗ α ∷ τ) eq
    with map-just (consᵗ X α)
                  (amguᶜ k (szᵗ τ p) rg (C [ X forᵗ α ]ᶜ) (D [ X forᵗ α ]ᶜ) (Θ' , τ)) eq
  ... | (Θ₂ , τ') , q , refl = descᵗ (eqᶜ C D) X α τ τ'
      (amguᶜ-sound k (szᵗ τ p) rg (C [ X forᵗ α ]ᶜ) (D [ X forᵗ α ]ᶜ) τ q)
  amguᶜ-sound (suc k) p rg C D {Θ'} (X /ʳ i ∷ τ) eq
    with map-just (consʳ X i)
                  (amguᶜ k (szʳ τ p) rg (C [ X forʳ i ]ᶜ) (D [ X forʳ i ]ᶜ) (Θ' , τ)) eq
  ... | (Θ₂ , τ') , q , refl = descʳ (eqᶜ C D) X i τ τ'
      (amguᶜ-sound k (szʳ τ p) rg (C [ X forʳ i ]ᶜ) (D [ X forʳ i ]ᶜ) τ q)
  amguᶜ-sound (suc k) p rg C D {Θ'} (X /ᵉ i ∷ τ) eq
    with map-just (consᵉ X i)
                  (amguᶜ k (szᵉ τ p) (popʳᵍ τ i rg) (C [ X forᵉ i ]ᶜ) (D [ X forᵉ i ]ᶜ) (Θ' , τ)) eq
  ... | (Θ₂ , τ') , q , refl = descᵉ (eqᶜ C D) X i τ τ'
      (amguᶜ-sound k (szᵉ τ p) (popʳᵍ τ i rg) (C [ X forᵉ i ]ᶜ) (D [ X forᵉ i ]ᶜ) τ q)
  amguᶜ-sound zero p rg C D (X /ᵗ α ∷ τ) eq = sz0ᵗ τ p
  amguᶜ-sound zero p rg C D (X /ʳ i ∷ τ) eq = sz0ʳ τ p
  amguᶜ-sound zero p rg C D (X /ᵉ i ∷ τ) eq = sz0ᵉ τ p

  amguᶜ-sound {Θ} (suc k) p rg (A ‼ ε) (B ‼ ε') anil eq =
    seq-sound (amguᵛ (suc k) p rg A B (Θ , anil)) (amguᵉ (suc k) p rg ε ε')
              (amguᵛ-sound (suc k) p rg A B anil) (amguᵉ-sound (suc k) p rg ε ε')
              (cong₂ _‼_) eq
  amguᶜ-sound {Θ} zero p rg (A ‼ ε) (B ‼ ε') anil eq =
    seq-sound (amguᵛ zero p rg A B (Θ , anil)) (amguᵉ zero p rg ε ε')
              (amguᵛ-sound zero p rg A B anil) (amguᵉ-sound zero p rg ε ε')
              (cong₂ _‼_) eq

  -- resource grades

  amguʳ-sound (suc k) p rg ρ₀ ρ₁ {Θ'} (X /ᵗ α ∷ τ) eq
    with map-just (consᵗ X α)
                  (amguʳ k (szᵗ τ p) rg (ρ₀ [ X forᵗ α ]ʳ) (ρ₁ [ X forᵗ α ]ʳ) (Θ' , τ)) eq
  ... | (Θ₂ , τ') , q , refl = descᵗ (eqʳ ρ₀ ρ₁) X α τ τ'
      (amguʳ-sound k (szᵗ τ p) rg (ρ₀ [ X forᵗ α ]ʳ) (ρ₁ [ X forᵗ α ]ʳ) τ q)
  amguʳ-sound (suc k) p rg ρ₀ ρ₁ {Θ'} (X /ʳ i ∷ τ) eq
    with map-just (consʳ X i)
                  (amguʳ k (szʳ τ p) rg (ρ₀ [ X forʳ i ]ʳ) (ρ₁ [ X forʳ i ]ʳ) (Θ' , τ)) eq
  ... | (Θ₂ , τ') , q , refl = descʳ (eqʳ ρ₀ ρ₁) X i τ τ'
      (amguʳ-sound k (szʳ τ p) rg (ρ₀ [ X forʳ i ]ʳ) (ρ₁ [ X forʳ i ]ʳ) τ q)
  amguʳ-sound (suc k) p rg ρ₀ ρ₁ {Θ'} (X /ᵉ i ∷ τ) eq
    with map-just (consᵉ X i)
                  (amguʳ k (szᵉ τ p) (popʳᵍ τ i rg) (ρ₀ [ X forᵉ i ]ʳ) (ρ₁ [ X forᵉ i ]ʳ) (Θ' , τ)) eq
  ... | (Θ₂ , τ') , q , refl = descᵉ (eqʳ ρ₀ ρ₁) X i τ τ'
      (amguʳ-sound k (szᵉ τ p) (popʳᵍ τ i rg) (ρ₀ [ X forᵉ i ]ʳ) (ρ₁ [ X forᵉ i ]ʳ) τ q)
  amguʳ-sound zero p rg ρ₀ ρ₁ (X /ᵗ α ∷ τ) eq = sz0ᵗ τ p
  amguʳ-sound zero p rg ρ₀ ρ₁ (X /ʳ i ∷ τ) eq = sz0ʳ τ p
  amguʳ-sound zero p rg ρ₀ ρ₁ (X /ᵉ i ∷ τ) eq = sz0ᵉ τ p

  amguʳ-sound (suc k) p rg (rvar i) (rvar j) anil eq = flexFlexʳ-sound i j eq
  amguʳ-sound (suc k) p rg (rvar i) (rconst d) anil eq = flexʳ-sound i (rconst d) eq
  amguʳ-sound (suc k) p rg (rvar i) (ρ₁' ·̂ᵣ ρ₂') anil eq = flexʳ-sound i (ρ₁' ·̂ᵣ ρ₂') eq
  amguʳ-sound (suc k) p rg (rvar i) ∣ ε' ∣̂ᵉ anil eq = flexʳ-sound i ∣ ε' ∣̂ᵉ eq
  amguʳ-sound (suc k) p rg (rconst c) (rvar j) anil eq = Sound-map sym (flexʳ-sound j (rconst c) eq)
  amguʳ-sound (suc k) p rg (ρ₁ ·̂ᵣ ρ₂) (rvar j) anil eq = Sound-map sym (flexʳ-sound j (ρ₁ ·̂ᵣ ρ₂) eq)
  amguʳ-sound (suc k) p rg ∣ ε ∣̂ᵉ (rvar j) anil eq = Sound-map sym (flexʳ-sound j ∣ ε ∣̂ᵉ eq)
  amguʳ-sound {Θ} (suc k) p rg (rconst c) (rconst d) anil eq
    with dec-if (c ≡ᵣ? d) (just (Θ , anil)) nothing eq
  ... | inj₁ (r , refl) = sound anil refl (cong rconst r)
  ... | inj₂ ()
  amguʳ-sound (suc k) p rg (rconst c) (ρ₁' ·̂ᵣ ρ₂') anil ()
  amguʳ-sound (suc k) p rg (rconst c) ∣ ε' ∣̂ᵉ anil ()
  amguʳ-sound (suc k) p rg (ρ₁ ·̂ᵣ ρ₂) (rconst d) anil ()
  amguʳ-sound {Θ} (suc k) p rg (ρ₁ ·̂ᵣ ρ₂) (ρ₁' ·̂ᵣ ρ₂') anil eq =
    seq-sound (amguʳ (suc k) p rg ρ₁ ρ₁' (Θ , anil)) (amguʳ (suc k) p rg ρ₂ ρ₂')
              (amguʳ-sound (suc k) p rg ρ₁ ρ₁' anil) (amguʳ-sound (suc k) p rg ρ₂ ρ₂')
              (cong₂ _·̂ᵣ_) eq
  amguʳ-sound (suc k) p rg (ρ₁ ·̂ᵣ ρ₂) ∣ ε' ∣̂ᵉ anil ()
  amguʳ-sound (suc k) p rg ∣ ε ∣̂ᵉ (rconst d) anil ()
  amguʳ-sound (suc k) p rg ∣ ε ∣̂ᵉ (ρ₁' ·̂ᵣ ρ₂') anil ()
  amguʳ-sound (suc k) p rg ∣ ε ∣̂ᵉ ∣ ε' ∣̂ᵉ anil eq =
    Sound-map (cong ∣_∣̂ᵉ) (amguᵉ-sound (suc k) p rg ε ε' anil eq)

  amguʳ-sound zero p rg (rvar i) (rvar j) anil eq = flexFlexʳ-sound i j eq
  amguʳ-sound zero p rg (rvar i) (rconst d) anil eq = flexʳ-sound i (rconst d) eq
  amguʳ-sound zero p rg (rvar i) (ρ₁' ·̂ᵣ ρ₂') anil eq = flexʳ-sound i (ρ₁' ·̂ᵣ ρ₂') eq
  amguʳ-sound zero p rg (rvar i) ∣ ε' ∣̂ᵉ anil eq = flexʳ-sound i ∣ ε' ∣̂ᵉ eq
  amguʳ-sound zero p rg (rconst c) (rvar j) anil eq = Sound-map sym (flexʳ-sound j (rconst c) eq)
  amguʳ-sound zero p rg (ρ₁ ·̂ᵣ ρ₂) (rvar j) anil eq = Sound-map sym (flexʳ-sound j (ρ₁ ·̂ᵣ ρ₂) eq)
  amguʳ-sound zero p rg ∣ ε ∣̂ᵉ (rvar j) anil eq = Sound-map sym (flexʳ-sound j ∣ ε ∣̂ᵉ eq)
  amguʳ-sound {Θ} zero p rg (rconst c) (rconst d) anil eq
    with dec-if (c ≡ᵣ? d) (just (Θ , anil)) nothing eq
  ... | inj₁ (r , refl) = sound anil refl (cong rconst r)
  ... | inj₂ ()
  amguʳ-sound zero p rg (rconst c) (ρ₁' ·̂ᵣ ρ₂') anil ()
  amguʳ-sound zero p rg (rconst c) ∣ ε' ∣̂ᵉ anil ()
  amguʳ-sound zero p rg (ρ₁ ·̂ᵣ ρ₂) (rconst d) anil ()
  amguʳ-sound {Θ} zero p rg (ρ₁ ·̂ᵣ ρ₂) (ρ₁' ·̂ᵣ ρ₂') anil eq =
    seq-sound (amguʳ zero p rg ρ₁ ρ₁' (Θ , anil)) (amguʳ zero p rg ρ₂ ρ₂')
              (amguʳ-sound zero p rg ρ₁ ρ₁' anil) (amguʳ-sound zero p rg ρ₂ ρ₂')
              (cong₂ _·̂ᵣ_) eq
  amguʳ-sound zero p rg (ρ₁ ·̂ᵣ ρ₂) ∣ ε' ∣̂ᵉ anil ()
  amguʳ-sound zero p rg ∣ ε ∣̂ᵉ (rconst d) anil ()
  amguʳ-sound zero p rg ∣ ε ∣̂ᵉ (ρ₁' ·̂ᵣ ρ₂') anil ()
  amguʳ-sound zero p rg ∣ ε ∣̂ᵉ ∣ ε' ∣̂ᵉ anil eq =
    Sound-map (cong ∣_∣̂ᵉ) (amguᵉ-sound zero p rg ε ε' anil eq)

  -- effect grades

  amguᵉ-sound (suc k) p rg ε ε' {Θ'} (X /ᵗ α ∷ τ) eq
    with map-just (consᵗ X α)
                  (amguᵉ k (szᵗ τ p) rg (ε [ X forᵗ α ]ᵉ) (ε' [ X forᵗ α ]ᵉ) (Θ' , τ)) eq
  ... | (Θ₂ , τ') , q , refl = descᵗ (eqᵉ ε ε') X α τ τ'
      (amguᵉ-sound k (szᵗ τ p) rg (ε [ X forᵗ α ]ᵉ) (ε' [ X forᵗ α ]ᵉ) τ q)
  amguᵉ-sound (suc k) p rg ε ε' {Θ'} (X /ʳ i ∷ τ) eq
    with map-just (consʳ X i)
                  (amguᵉ k (szʳ τ p) rg (ε [ X forʳ i ]ᵉ) (ε' [ X forʳ i ]ᵉ) (Θ' , τ)) eq
  ... | (Θ₂ , τ') , q , refl = descʳ (eqᵉ ε ε') X i τ τ'
      (amguᵉ-sound k (szʳ τ p) rg (ε [ X forʳ i ]ᵉ) (ε' [ X forʳ i ]ᵉ) τ q)
  amguᵉ-sound (suc k) p rg ε ε' {Θ'} (X /ᵉ i ∷ τ) eq
    with map-just (consᵉ X i)
                  (amguᵉ k (szᵉ τ p) (popʳᵍ τ i rg) (ε [ X forᵉ i ]ᵉ) (ε' [ X forᵉ i ]ᵉ) (Θ' , τ)) eq
  ... | (Θ₂ , τ') , q , refl = descᵉ (eqᵉ ε ε') X i τ τ'
      (amguᵉ-sound k (szᵉ τ p) (popʳᵍ τ i rg) (ε [ X forᵉ i ]ᵉ) (ε' [ X forᵉ i ]ᵉ) τ q)
  amguᵉ-sound zero p rg ε ε' (X /ᵗ α ∷ τ) eq = sz0ᵗ τ p
  amguᵉ-sound zero p rg ε ε' (X /ʳ i ∷ τ) eq = sz0ʳ τ p
  amguᵉ-sound zero p rg ε ε' (X /ᵉ i ∷ τ) eq = sz0ᵉ τ p

  amguᵉ-sound (suc k) p rg (evar i) (evar j) anil eq = flexFlexᵉ-sound rg i j eq
  amguᵉ-sound (suc k) p rg (evar i) (econst d) anil eq = flexᵉ-sound rg i (econst d) eq
  amguᵉ-sound (suc k) p rg (evar i) (ε₁' ·̂ₑ ε₂') anil eq = flexᵉ-sound rg i (ε₁' ·̂ₑ ε₂') eq
  amguᵉ-sound (suc k) p rg (econst c) (evar j) anil eq = Sound-map sym (flexᵉ-sound rg j (econst c) eq)
  amguᵉ-sound (suc k) p rg (ε₁ ·̂ₑ ε₂) (evar j) anil eq = Sound-map sym (flexᵉ-sound rg j (ε₁ ·̂ₑ ε₂) eq)
  amguᵉ-sound {Θ} (suc k) p rg (econst c) (econst d) anil eq
    with dec-if (c ≡ₑ? d) (just (Θ , anil)) nothing eq
  ... | inj₁ (r , refl) = sound anil refl (cong econst r)
  ... | inj₂ ()
  amguᵉ-sound (suc k) p rg (econst c) (ε₁' ·̂ₑ ε₂') anil ()
  amguᵉ-sound (suc k) p rg (ε₁ ·̂ₑ ε₂) (econst d) anil ()
  amguᵉ-sound {Θ} (suc k) p rg (ε₁ ·̂ₑ ε₂) (ε₁' ·̂ₑ ε₂') anil eq =
    seq-sound (amguᵉ (suc k) p rg ε₁ ε₁' (Θ , anil)) (amguᵉ (suc k) p rg ε₂ ε₂')
              (amguᵉ-sound (suc k) p rg ε₁ ε₁' anil) (amguᵉ-sound (suc k) p rg ε₂ ε₂')
              (cong₂ _·̂ₑ_) eq

  amguᵉ-sound zero p rg (evar i) (evar j) anil eq = flexFlexᵉ-sound rg i j eq
  amguᵉ-sound zero p rg (evar i) (econst d) anil eq = flexᵉ-sound rg i (econst d) eq
  amguᵉ-sound zero p rg (evar i) (ε₁' ·̂ₑ ε₂') anil eq = flexᵉ-sound rg i (ε₁' ·̂ₑ ε₂') eq
  amguᵉ-sound zero p rg (econst c) (evar j) anil eq = Sound-map sym (flexᵉ-sound rg j (econst c) eq)
  amguᵉ-sound zero p rg (ε₁ ·̂ₑ ε₂) (evar j) anil eq = Sound-map sym (flexᵉ-sound rg j (ε₁ ·̂ₑ ε₂) eq)
  amguᵉ-sound {Θ} zero p rg (econst c) (econst d) anil eq
    with dec-if (c ≡ₑ? d) (just (Θ , anil)) nothing eq
  ... | inj₁ (r , refl) = sound anil refl (cong econst r)
  ... | inj₂ ()
  amguᵉ-sound zero p rg (econst c) (ε₁' ·̂ₑ ε₂') anil ()
  amguᵉ-sound zero p rg (ε₁ ·̂ₑ ε₂) (econst d) anil ()
  amguᵉ-sound {Θ} zero p rg (ε₁ ·̂ₑ ε₂) (ε₁' ·̂ₑ ε₂') anil eq =
    seq-sound (amguᵉ zero p rg ε₁ ε₁' (Θ , anil)) (amguᵉ zero p rg ε₂ ε₂')
              (amguᵉ-sound zero p rg ε₁ ε₁' anil) (amguᵉ-sound zero p rg ε₂ ε₂')
              (cong₂ _·̂ₑ_) eq

--------------------------------------------------------------
-- Soundness of the equation solver                          --
--------------------------------------------------------------

amguᴱ-sound : ∀ {Θ} → (rg : Rig Θ) → (e : Eqn Θ) → {Θ' Θ'' : Scope}
            → (ρ : AList Θ Θ') → {ρ'' : AList Θ Θ''}
            → amguᴱ rg e (Θ' , ρ) ≡ just (Θ'' , ρ'') → Sound e ρ ρ''
amguᴱ-sound {Θ} rg (eqᵛ A B)  ρ eq = amguᵛ-sound (Sz Θ) refl rg A B ρ eq
amguᴱ-sound {Θ} rg (eqᶜ C D)  ρ eq = amguᶜ-sound (Sz Θ) refl rg C D ρ eq
amguᴱ-sound {Θ} rg (eqʳ ρ₀ ρ₁) ρ eq = amguʳ-sound (Sz Θ) refl rg ρ₀ ρ₁ ρ eq
amguᴱ-sound {Θ} rg (eqᵉ ε ε')  ρ eq = amguᵉ-sound (Sz Θ) refl rg ε ε' ρ eq

unifyᴬ-sound : ∀ {Θ} → (rg : Rig Θ) → (es : Eqns Θ) → {Θ' Θ'' : Scope}
             → (ρ : AList Θ Θ') → {ρ'' : AList Θ Θ''}
             → unifyᴬ rg es (Θ' , ρ) ≡ just (Θ'' , ρ'')
             → Σ[ ρ⁺ ∈ AList Θ' Θ'' ] ((ρ'' ≡ ρ⁺ ++ᴬ ρ) × Unifies es ⟦ ρ'' ⟧ᴬ)
unifyᴬ-sound rg []       ρ refl = anil , sym (anil-++ᴬ ρ) , tt
unifyᴬ-sound {Θ} rg (e ∷ es) {Θ'} ρ eq
  with bind-just (amguᴱ rg e (Θ' , ρ)) (unifyᴬ rg es) eq
... | (Θ₁ , ρ₁) , q₁ , q₂ with amguᴱ-sound rg e ρ q₁ | unifyᴬ-sound rg es ρ₁ q₂
...   | sound ρ⁺₁ r₁ u₁ | ρ⁺₂ , r₂ , us =
        ρ⁺₂ ++ᴬ ρ⁺₁ ,
        trans r₂ (trans (cong (ρ⁺₂ ++ᴬ_) r₁) (sym (++ᴬ-assoc ρ⁺₂ ρ⁺₁ ρ))) ,
        (subst (λ z → Unifies¹ e ⟦ z ⟧ᴬ) (sym r₂) (mono++ ρ⁺₂ e u₁) , us)

unify-sound : ∀ {Θ Θ⁺} → (rg : Rig Θ) → (es : Eqns Θ) → {ρ : AList Θ Θ⁺}
            → unify rg es ≡ just (Θ⁺ , ρ) → Unifies es ⟦ ρ ⟧ᴬ
unify-sound {Θ} rg es eq with unifyᴬ-sound rg es anil eq
... | _ , _ , us = us

--------------------------------------------------------------
-- Sanity check                                              --
--------------------------------------------------------------

private

  -- one type variable, bound to `Unit` by the only equation

  es₁ : Eqns (∅ˢ +ty)
  es₁ = eqᵛ (tvar (newᵗ {∅ˢ})) Unit ∷ []

  ex-tvar : Unifies es₁ ⟦ Unit /ᵗ newᵗ {∅ˢ} ∷ anil ⟧ᴬ
  ex-tvar = unify-sound [] es₁ refl

  -- a box type against a box type: the equation is decomposed, the
  -- grade variable is bound, and the second call descends the store

  es₂ : Eqns (∅ˢ +r)
  es₂ = eqᵛ ([ rvar (newʳ {∅ˢ}) ] Unit) ([ ûᵣ ] Unit) ∷ []

  ex-box : Unifies es₂ ⟦ ûᵣ /ʳ newʳ {∅ˢ} ∷ anil ⟧ᴬ
  ex-box = unify-sound [] es₂ refl
