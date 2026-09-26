------------------------------------------------------------------
-- Expansion and decomposition keep the invariants                --
--                                                                --
-- `expandSub` renames every grade unknown and sends a type       --
-- variable to a type variable or to a decoration whose grades    --
-- are fresh unknowns, so it is good against any substitution     --
-- (`expandSub-good`). The orderings a subtyping demand           --
-- decomposes to are between grades of its two types, so good     --
-- ones (`subDec-good`). Hence the subtyping step and `reexpand`  --
-- keep `Inv` by a good move (`inv-sub`, `inv-reexpand`).         --
------------------------------------------------------------------

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using ([_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Vec.Base using (Vec; []; _∷_; lookup; tabulate)

open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Invariants.Expand (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (_≡ᵇ?_)

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S using (mapᵖ)

open import TypeInference.SolverImpl.Core.Skel      S using (Skel; svar?)
open import TypeInference.SolverImpl.Core.SkelUnify S using (unifyᵏ; ⟦_⟧ᴷ)
open import TypeInference.SolverImpl.Core.Decorate  S
open import TypeInference.SolverImpl.Core.Rigid     S using (zip₂-just)
open import TypeInference.SolverImpl.Resid S
open import TypeInference.SolverImpl.State S using (St; st; θ; res; rig; transRig)
open import TypeInference.SolverImpl.Invariants.Outer    S
open import TypeInference.SolverImpl.Invariants.Residual S

------------------------------------------------------------------------
-- Renamings

record IsRen {Ψ Ψ'} (σ : Subst Ψ Ψ') : Set where
  constructor mkRen
  field
    renᵗ : ∀ α → Σ[ β ∈ TyVar Ψ' ] (sTy σ α ≡ tvar β)
    renʳ : ∀ i → Σ[ j ∈ RVar Ψ' ] (sR σ i ≡ rvar j)
    renᵉ : ∀ i → Σ[ j ∈ EVar Ψ' ] (sE σ i ≡ evar j)

open IsRen public

ren-id : ∀ {Ψ} → IsRen (idˢ {Ψ})
ren-id = mkRen (λ α → α , refl) (λ i → i , refl) (λ i → i , refl)

ren-wkᵗ : ∀ {Ψ} → IsRen (wkˢᵗ {Ψ})
ren-wkᵗ {Ψ} = mkRen (λ α → wkᵗ-tv Ψ α , refl) (λ i → i , refl) (λ i → i , refl)

ren-wkʳ : ∀ {Ψ} → IsRen (wkˢʳ {Ψ})
ren-wkʳ {Ψ} = mkRen (λ α → α , refl) (λ i → wkʳ-rv Ψ i , refl) (λ i → i , refl)

ren-wkᵉ : ∀ {Ψ} → IsRen (wkˢᵉ {Ψ})
ren-wkᵉ {Ψ} = mkRen (λ α → α , refl) (λ i → i , refl) (λ i → wkᵉ-ev Ψ i , refl)

ren-⨟ : ∀ {Ψ Ψ' Ψ''} {σ : Subst Ψ Ψ'} {τ : Subst Ψ' Ψ''} → IsRen σ → IsRen τ → IsRen (σ ⨟ˢ τ)
ren-⨟ {Ψ'' = Ψ''} {σ = σ} {τ} r q = mkRen t rr e
  where
    t : ∀ α → Σ[ β ∈ TyVar Ψ'' ] (sTy σ α [ τ ]ᵛ ≡ tvar β)
    t α with sTy σ α | renᵗ r α
    ... | .(tvar β) | β , refl = renᵗ q β

    rr : ∀ i → Σ[ j ∈ RVar Ψ'' ] (sR σ i [ τ ]ʳ ≡ rvar j)
    rr i with sR σ i | renʳ r i
    ... | .(rvar j) | j , refl = renʳ q j

    e : ∀ i → Σ[ j ∈ EVar Ψ'' ] (sE σ i [ τ ]ᵉ ≡ evar j)
    e i with sE σ i | renᵉ r i
    ... | .(evar j) | j , refl = renᵉ q j

GV-isRen : ∀ {Θ Ψ Ψ'} {P : Subst Θ Ψ'} {σ : Subst Ψ Ψ'} → IsRen σ → GV P σ
GV-isRen r = GV-ren (renᵗ r) (renʳ r) (renᵉ r)

------------------------------------------------------------------------
-- Types every grade of which is an unknown

mutual

  Wholeᵛ : ∀ {Ψ} → OVType Ψ → Set
  Wholeᵛ (tvar α)  = ⊤
  Wholeᵛ (Base b)  = ⊤
  Wholeᵛ Unit      = ⊤
  Wholeᵛ Bool      = ⊤
  Wholeᵛ Empty     = ⊤
  Wholeᵛ (A |×| B) = Wholeᵛ A × Wholeᵛ B
  Wholeᵛ (A ⇒ C)   = Wholeᵛ A × Wholeᶜ C
  Wholeᵛ {Ψ} ([ ρ ] A) = (Σ[ k ∈ RVar Ψ ] (ρ ≡ rvar k)) × Wholeᵛ A

  Wholeᶜ : ∀ {Ψ} → OCType Ψ → Set
  Wholeᶜ {Ψ} (A ‼ ε) = Wholeᵛ A × (Σ[ k ∈ EVar Ψ ] (ε ≡ evar k))

module _ {Θ Ψ} {P : Subst Θ Ψ} where

  mutual

    whole-goodᵛ : ∀ A → Wholeᵛ A → TyGoodᵛ P A
    whole-goodᵛ (tvar α)  w       = tt
    whole-goodᵛ (Base b)  w       = tt
    whole-goodᵛ Unit      w       = tt
    whole-goodᵛ Bool      w       = tt
    whole-goodᵛ Empty     w       = tt
    whole-goodᵛ (A |×| B) (u , v) = whole-goodᵛ A u , whole-goodᵛ B v
    whole-goodᵛ (A ⇒ C)   (u , v) = whole-goodᵛ A u , whole-goodᶜ C v
    whole-goodᵛ ([ .(rvar k) ] A) ((k , refl) , v) = whole k , whole-goodᵛ A v

    whole-goodᶜ : ∀ C → Wholeᶜ C → TyGoodᶜ P C
    whole-goodᶜ (A ‼ .(evar k)) (u , (k , refl)) = whole-goodᵛ A u , whole k

module _ {Ψ Ψ'} {σ : Subst Ψ Ψ'} (r : IsRen σ) where

  mutual

    whole-renᵛ : ∀ A → Wholeᵛ A → Wholeᵛ (A [ σ ]ᵛ)
    whole-renᵛ (tvar α)  w with sTy σ α | renᵗ r α
    ... | .(tvar β) | β , refl = tt
    whole-renᵛ (Base b)  w       = tt
    whole-renᵛ Unit      w       = tt
    whole-renᵛ Bool      w       = tt
    whole-renᵛ Empty     w       = tt
    whole-renᵛ (A |×| B) (u , v) = whole-renᵛ A u , whole-renᵛ B v
    whole-renᵛ (A ⇒ C)   (u , v) = whole-renᵛ A u , whole-renᶜ C v
    whole-renᵛ ([ .(rvar k) ] A) ((k , refl) , v) = renʳ r k , whole-renᵛ A v

    whole-renᶜ : ∀ C → Wholeᶜ C → Wholeᶜ (C [ σ ]ᶜ)
    whole-renᶜ (A ‼ .(evar k)) (u , (k , refl)) = whole-renᵛ A u , renᵉ r k

------------------------------------------------------------------------
-- The expansion is good

-- a decoration: the old scope renamed, the type whole

decorate-good : ∀ {m} → (Ψ : Scope) → (t : Skel m)
              → IsRen (proj₁ (proj₂ (decorate Ψ t))) × Wholeᵛ (proj₂ (proj₂ (decorate Ψ t)))
decorate-good Ψ (Skel.svar γ)  = ren-wkᵗ , tt
decorate-good Ψ (Skel.sBase b) = ren-id , tt
decorate-good Ψ Skel.sUnit     = ren-id , tt
decorate-good Ψ Skel.sBool     = ren-id , tt
decorate-good Ψ Skel.sEmpty    = ren-id , tt
decorate-good Ψ (t Skel.s× u) with decorate Ψ t | decorate-good Ψ t
... | Ψ₁ , w₁ , A | r₁ , h₁ with decorate Ψ₁ u | decorate-good Ψ₁ u
...   | Ψ₂ , w₂ , B | r₂ , h₂ = ren-⨟ r₁ r₂ , whole-renᵛ r₂ A h₁ , h₂
decorate-good Ψ (t Skel.s⇒ u) with decorate Ψ t | decorate-good Ψ t
... | Ψ₁ , w₁ , A | r₁ , h₁ with decorate Ψ₁ u | decorate-good Ψ₁ u
...   | Ψ₂ , w₂ , B | r₂ , h₂ =
        ren-⨟ (ren-⨟ r₁ r₂) ren-wkᵉ ,
        subst Wholeᵛ (wkˢᵉ-v (A [ w₂ ]ᵛ)) (whole-renᵛ ren-wkᵉ (A [ w₂ ]ᵛ) (whole-renᵛ r₂ A h₁)) ,
        subst Wholeᵛ (wkˢᵉ-v B) (whole-renᵛ ren-wkᵉ B h₂) , (_ , refl)
decorate-good Ψ (Skel.sBox t) with decorate Ψ t | decorate-good Ψ t
... | Ψ₁ , w₁ , A | r₁ , h₁ =
      ren-⨟ r₁ ren-wkʳ , (_ , refl) , subst Wholeᵛ (wkˢʳ-v A) (whole-renᵛ ren-wkʳ A h₁)

JustWhole : ∀ {Ψ} → Maybe (OVType Ψ) → Set
JustWhole (just A) = Wholeᵛ A
JustWhole nothing  = ⊤

decorate*-good : ∀ {m k} → (Ψ : Scope) → (ts : Vec (Skel m) k)
               → IsRen (proj₁ (proj₂ (decorate* Ψ ts)))
               × (∀ i → JustWhole (lookup (proj₂ (proj₂ (decorate* Ψ ts))) i))
decorate*-good Ψ []       = ren-id , λ ()
decorate*-good Ψ (t ∷ ts) with svar? t
... | just γ with decorate* Ψ ts | decorate*-good Ψ ts
...   | Ψ' , w , As | r , h = r , λ { zero → tt ; (suc i) → h i }
decorate*-good Ψ (t ∷ ts) | nothing with decorate Ψ t | decorate-good Ψ t
... | Ψ₁ , w₁ , A | r₁ , h₁ with decorate* Ψ₁ ts | decorate*-good Ψ₁ ts
...   | Ψ₂ , w₂ , As | r₂ , h₂ =
        ren-⨟ r₁ r₂ , λ { zero → whole-renᵛ r₂ A h₁ ; (suc i) → h₂ i }

expandᵏ-good : ∀ {m Θ} → (Ψ : Scope) → (σ : Fin (nTy Ψ) → Skel m)
             → {P : Subst Θ (proj₁ (expandᵏ Ψ σ))} → GV P (proj₂ (expandᵏ Ψ σ))
expandᵏ-good Ψ σ {P} with decorate* Ψ (tabulate σ) | decorate*-good Ψ (tabulate σ)
... | Ψ' , w , As | r , h = mkGV t (λ i → gvʳ (GV-isRen {P = P} r) i) (λ i → gvᵉ (GV-isRen {P = P} r) i)
  where
    t : ∀ α → TyGoodᵛ P (maybe′ (λ A → A) (sTy w α) (lookup As α))
    t α with lookup As α | h α
    ... | just A  | hA = whole-goodᵛ A hA
    ... | nothing | _  = gvᵗ (GV-isRen {P = P} r) α

private
  ⊥just : ∀ {X Y : Set} {x : X} → nothing ≡ just x → Y
  ⊥just ()

expandSub-good : ∀ {Θ Ψ} → (l : List (OVType Ψ × OVType Ψ)) → ∀ {Ψ'} {δ : Subst Ψ Ψ'}
               → expandSub l ≡ just (Ψ' , δ) → {P : Subst Θ Ψ'} → GV P δ
expandSub-good {Ψ = Ψ} l eq with unifyᵏ (skelEqns l)
... | nothing = ⊥just eq
... | just (m , τ) with eq
...   | refl = expandᵏ-good Ψ ⟦ τ ⟧ᴷ

------------------------------------------------------------------------
-- Decomposition: the orderings are between grades of the two types

record AtomsGood {Θ Ψ} (P : Subst Θ Ψ) (a : SubAtoms Ψ) : Set where
  constructor mkAG
  field
    agʳ : ∀ {x y} → (x , y) ∈ aordᵣ a → Goodᵣ P y
    agᵉ : ∀ {x y} → (x , y) ∈ aordₑ a → Goodₑ P y

open AtomsGood public

ag-none : ∀ {Θ Ψ} {P : Subst Θ Ψ} → AtomsGood P (noAtoms {Ψ})
ag-none = mkAG (λ ()) (λ ())

ag-∪ : ∀ {Θ Ψ} {P : Subst Θ Ψ} {a b : SubAtoms Ψ}
     → AtomsGood P a → AtomsGood P b → AtomsGood P (a ∪ᴬ b)
ag-∪ {a = a} g h = mkAG (λ m → [ agʳ g , agʳ h ]′ (∈-++⁻ (aordᵣ a) m))
                        (λ m → [ agᵉ g , agᵉ h ]′ (∈-++⁻ (aordₑ a) m))

module _ {Θ Ψ} (P : Subst Θ Ψ) where

  mutual

    subDec-good : ∀ (A B : OVType Ψ) → TyGoodᵛ P A → TyGoodᵛ P B
                → ∀ {d} → subDec A B ≡ just d → AtomsGood P (atomsOf d)
    subDec-good (tvar α) (tvar β) gA gB refl = mkAG (λ ()) (λ ())
    subDec-good (Base b) (Base b') gA gB eq with b ≡ᵇ? b'
    ... | yes refl with eq
    ...   | refl = ag-none
    subDec-good (Base b) (Base b') gA gB () | no _
    subDec-good Unit  Unit  gA gB refl = ag-none
    subDec-good Bool  Bool  gA gB refl = ag-none
    subDec-good Empty Empty gA gB refl = ag-none
    subDec-good (A |×| B) (A' |×| B') (gA , gB) (gA' , gB') eq
      with zip₂-just pairᴰ (subDec A A') (subDec B B') eq
    ... | d₁ , d₂ , e₁ , e₂ , refl = ag-∪ (subDec-good A A' gA gA' e₁) (subDec-good B B' gB gB' e₂)
    subDec-good (A ⇒ C) (A' ⇒ C') (gA , gC) (gA' , gC') eq
      with zip₂-just arrᴰ (subDec A' A) (subDecᶜ C C') eq
    ... | d₁ , d₂ , e₁ , e₂ , refl = ag-∪ (subDec-good A' A gA' gA e₁) (subDecᶜ-good C C' gC gC' e₂)
    subDec-good ([ ρ ] A) ([ ρ' ] A') (gρ , gA) (gρ' , gA') eq
      with subDec A A' in e
    ... | just d with eq
    ...   | refl = ag-∪ (mkAG (λ { (here refl) → gρ }) (λ ())) (subDec-good A A' gA gA' e)
    subDec-good ([ ρ ] A) ([ ρ' ] A') (gρ , gA) (gρ' , gA') () | nothing
    subDec-good (tvar α) (Base b') gA gB ()
    subDec-good (tvar α) Unit gA gB ()
    subDec-good (tvar α) Bool gA gB ()
    subDec-good (tvar α) (A' |×| B') gA gB ()
    subDec-good (tvar α) Empty gA gB ()
    subDec-good (tvar α) (A' ⇒ C') gA gB ()
    subDec-good (tvar α) ([ ρ' ] A') gA gB ()
    subDec-good (Base b) (tvar β) gA gB ()
    subDec-good (Base b) Unit gA gB ()
    subDec-good (Base b) Bool gA gB ()
    subDec-good (Base b) (A' |×| B') gA gB ()
    subDec-good (Base b) Empty gA gB ()
    subDec-good (Base b) (A' ⇒ C') gA gB ()
    subDec-good (Base b) ([ ρ' ] A') gA gB ()
    subDec-good Unit (tvar β) gA gB ()
    subDec-good Unit (Base b') gA gB ()
    subDec-good Unit Bool gA gB ()
    subDec-good Unit (A' |×| B') gA gB ()
    subDec-good Unit Empty gA gB ()
    subDec-good Unit (A' ⇒ C') gA gB ()
    subDec-good Unit ([ ρ' ] A') gA gB ()
    subDec-good Bool (tvar β) gA gB ()
    subDec-good Bool (Base b') gA gB ()
    subDec-good Bool Unit gA gB ()
    subDec-good Bool (A' |×| B') gA gB ()
    subDec-good Bool Empty gA gB ()
    subDec-good Bool (A' ⇒ C') gA gB ()
    subDec-good Bool ([ ρ' ] A') gA gB ()
    subDec-good (A |×| B) (tvar β) gA gB ()
    subDec-good (A |×| B) (Base b') gA gB ()
    subDec-good (A |×| B) Unit gA gB ()
    subDec-good (A |×| B) Bool gA gB ()
    subDec-good (A |×| B) Empty gA gB ()
    subDec-good (A |×| B) (A' ⇒ C') gA gB ()
    subDec-good (A |×| B) ([ ρ' ] A') gA gB ()
    subDec-good Empty (tvar β) gA gB ()
    subDec-good Empty (Base b') gA gB ()
    subDec-good Empty Unit gA gB ()
    subDec-good Empty Bool gA gB ()
    subDec-good Empty (A' |×| B') gA gB ()
    subDec-good Empty (A' ⇒ C') gA gB ()
    subDec-good Empty ([ ρ' ] A') gA gB ()
    subDec-good (A ⇒ C) (tvar β) gA gB ()
    subDec-good (A ⇒ C) (Base b') gA gB ()
    subDec-good (A ⇒ C) Unit gA gB ()
    subDec-good (A ⇒ C) Bool gA gB ()
    subDec-good (A ⇒ C) (A' |×| B') gA gB ()
    subDec-good (A ⇒ C) Empty gA gB ()
    subDec-good (A ⇒ C) ([ ρ' ] A') gA gB ()
    subDec-good ([ ρ ] A) (tvar β) gA gB ()
    subDec-good ([ ρ ] A) (Base b') gA gB ()
    subDec-good ([ ρ ] A) Unit gA gB ()
    subDec-good ([ ρ ] A) Bool gA gB ()
    subDec-good ([ ρ ] A) (A' |×| B') gA gB ()
    subDec-good ([ ρ ] A) Empty gA gB ()
    subDec-good ([ ρ ] A) (A' ⇒ C') gA gB ()

    subDecᶜ-good : ∀ (C D : OCType Ψ) → TyGoodᶜ P C → TyGoodᶜ P D
                 → ∀ {d} → subDecᶜ C D ≡ just d → AtomsGood P (atomsOfᶜ d)
    subDecᶜ-good (A ‼ ε) (A' ‼ ε') (gA , gε) (gA' , gε') eq with subDec A A' in e
    ... | just d with eq
    ...   | refl = ag-∪ (subDec-good A A' gA gA' e) (mkAG (λ ()) (λ { (here refl) → gε' }))
    subDecᶜ-good (A ‼ ε) (A' ‼ ε') (gA , gε) (gA' , gε') () | nothing

  subsList-good : ∀ (l : List (OVType Ψ × OVType Ψ))
                → (∀ {A B} → (A , B) ∈ l → TyGoodᵛ P A × TyGoodᵛ P B)
                → ∀ {d} → subsList l ≡ just d → AtomsGood P (atomsOfˢ d)
  subsList-good []             g refl = ag-none
  subsList-good ((A , B) ∷ l) g eq with subDec A B in e₁ | subsList l in e₂
  ... | just d | just ds with eq
  ...   | refl = ag-∪ (subDec-good A B (proj₁ (g (here refl))) (proj₂ (g (here refl))) e₁)
                      (subsList-good l (λ m → g (there m)) e₂)
  subsList-good ((A , B) ∷ l) g () | just _  | nothing
  subsList-good ((A , B) ∷ l) g () | nothing | _

-- A residual with its demands decomposed, and the atoms of one demand

resinv-atomise : ∀ {Θ Ψ} {P : Subst Θ Ψ} → (R : Resid Ψ) → (d : SubsDec (ss R))
               → (t : EtsDec (ts R)) → AtomsGood P (atomsOfˢ d) → ResInv P R
               → ResInv P (atomiseᴿ R d t)
resinv-atomise R d t ag r =
  mkResInv sᵢ (λ m → [ I1′ʳ r , agʳ ag ]′ (∈-++⁻ (rs R) m))
              (λ m → [ I1′ᵉ r , agᵉ ag ]′ (∈-++⁻ (es R) m)) (I5 r)
  where
    sᵢ : ∀ {A B} → (A , B) ∈ map (mapᵖ tvar) (asubᵥ (atomsOfˢ d)) → _ × _
    sᵢ m with ∈-map⁻ (mapᵖ tvar) m
    ... | (α , β) , m₀ , refl = tt , tt

resinv-atoms : ∀ {Θ Ψ} {P : Subst Θ Ψ} → (a : SubAtoms Ψ) → AtomsGood P a → ResInv P (atomsᴿ a)
resinv-atoms a ag = mkResInv sᵢ (agʳ ag) (agᵉ ag) (λ ())
  where
    sᵢ : ∀ {A B} → (A , B) ∈ map (mapᵖ tvar) (asubᵥ a) → _ × _
    sᵢ m with ∈-map⁻ (mapᵖ tvar) m
    ... | (α , β) , m₀ , refl = tt , tt

------------------------------------------------------------------------
-- The two steps that expand

-- A subtyping atom: the state `solve` reaches, and its move `δ`

inv-sub : ∀ {Θ₀ Θ} (π : Subst Θ₀ Θ) (s : St Θ) (A B : OVType Θ)
        → Inv π s → TyGoodᵛ π A → TyGoodᵛ π B
        → ∀ {Ψ' δ} → expandSub ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) ≡ just (Ψ' , δ)
        → ∀ {d} → subDec (A [ θ s ]ᵛ [ δ ]ᵛ) (B [ θ s ]ᵛ [ δ ]ᵛ) ≡ just d
        → ∀ {e} → subsList (ss (res s [ δ ]ᴿ)) ≡ just e → (t : EtsDec (ts (res s [ δ ]ᴿ)))
        → Inv π (st Ψ' (θ s ⨟ˢ δ) (atomiseᴿ (res s [ δ ]ᴿ) e t ∪ᴿ atomsᴿ (atomsOf d))
                    (transRig δ (rig s)))
          × GV (π ⨟ˢ (θ s ⨟ˢ δ)) δ
inv-sub π s A B iv gA gB {δ = δ} eqx {d} eqd {e} eqs t =
  mkInv (GV-⊆ inc (GV-⨟ {P = P₀} (inv-θ iv) g))
        (resinv-⊆ inc (resinv-∪ r₂ (resinv-atoms (atomsOf d) ad))) ,
  GV-⊆ inc g
  where
    P₀ = π ⨟ˢ θ s

    g : GV (P₀ ⨟ˢ δ) δ
    g = expandSub-good ((A [ θ s ]ᵛ , B [ θ s ]ᵛ) ∷ ss (res s)) eqx

    r₁ = resinv-subst {P = P₀} g (inv-R iv)
    r₂ = resinv-atomise (res s [ δ ]ᴿ) e t
           (subsList-good (P₀ ⨟ˢ δ) (ss (res s [ δ ]ᴿ)) (inv-ss r₁) eqs) r₁
    tA = tygoodᵛ-⨟ {P = P₀} g (A [ θ s ]ᵛ) (tygoodᵛ-⨟ {P = π} (inv-θ iv) A gA)
    tB = tygoodᵛ-⨟ {P = P₀} g (B [ θ s ]ᵛ) (tygoodᵛ-⨟ {P = π} (inv-θ iv) B gB)
    ad = subDec-good (P₀ ⨟ˢ δ) (A [ θ s ]ᵛ [ δ ]ᵛ) (B [ θ s ]ᵛ [ δ ]ᵛ) tA tB eqd
    inc = ≐→⊆ᶠ (⨟-assoc π (θ s) δ)

-- `reexpand`: the state it reaches, and its move `δ`

inv-reexpand : ∀ {Θ₀ Θ} (π : Subst Θ₀ Θ) (s : St Θ) → Inv π s
             → ∀ {Ψ' δ} → expandSub (ss (res s)) ≡ just (Ψ' , δ)
             → ∀ {e} → subsList (ss (res s [ δ ]ᴿ)) ≡ just e → (t : EtsDec (ts (res s [ δ ]ᴿ)))
             → Inv π (st Ψ' (θ s ⨟ˢ δ) (atomiseᴿ (res s [ δ ]ᴿ) e t) (transRig δ (rig s)))
               × GV (π ⨟ˢ (θ s ⨟ˢ δ)) δ
inv-reexpand π s iv {δ = δ} eqx {e} eqs t =
  mkInv (GV-⊆ inc (GV-⨟ {P = P₀} (inv-θ iv) g))
        (resinv-⊆ inc (resinv-atomise (res s [ δ ]ᴿ) e t
                        (subsList-good (P₀ ⨟ˢ δ) (ss (res s [ δ ]ᴿ)) (inv-ss r₁) eqs) r₁)) ,
  GV-⊆ inc g
  where
    P₀ = π ⨟ˢ θ s

    g : GV (P₀ ⨟ˢ δ) δ
    g = expandSub-good (ss (res s)) eqx

    r₁ = resinv-subst {P = P₀} g (inv-R iv)
    inc = ≐→⊆ᶠ (⨟-assoc π (θ s) δ)
