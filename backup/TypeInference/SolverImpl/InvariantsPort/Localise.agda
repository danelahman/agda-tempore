------------------------------------------------------------------
-- Localisation keeps the residual invariant                      --
--                                                                --
-- Read against `P`, whose free unknowns are free in `O`. Each    --
-- step assigns local unknowns only, so it fixes `P`; a whole     --
-- greater side goes to an unknown, a constant, the cap (itself a --
-- greater side), or, for lowering, its ordering is dropped.      --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; reverse)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (_+_) renaming (zero to nzero; suc to nsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)

open import Reflection
  using (TC; Term; def; arg; hArg; vArg; unknown; reduce; inferType; unify; typeError; strErr;
         pure; _>>=_)
open import Relation.Nullary using (yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Invariants.Localise (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S using (Hyps; Is-just?; mapᵖ)

open import TypeInference.SolverImpl.Core.Occurs S using (occᵉ-e; occᵉ-r; occᵉ-v; occʳ-r; occʳ-v)
open import TypeInference.SolverImpl.Core.Rigid S using (∨-left; ∨-right; true-dec)
open import TypeInference.SolverImpl.Deferred S using (_[_]ᵈ; stills?; dir↓; dir↑)
open import TypeInference.SolverImpl.Resid    S
open import TypeInference.SolverImpl.Bounds   S
open import TypeInference.SolverImpl.Vars     S
  using (Vars; vars; _⊆ᵛ_; mk⊆ᵛ; Fixes; mkFixes; fixᵗ; fixʳ; fixᵉ; fix-v; fix-r; fix-e;
         fixes-updᵉ; fixes-updʳ; ≟-self)
open import TypeInference.SolverImpl.Localise S
open import TypeInference.SolverImpl.Invariants.Outer    S
open import TypeInference.SolverImpl.Invariants.Residual S
open import TypeInference.SolverImpl.Invariants.Canon    S using (resinv-normal)

private
  t≢f : true ≡ false → ⊥
  t≢f ()

  nothing≢just : ∀ {X : Set} {x : X} → nothing ≡ just x → ⊥
  nothing≢just ()

------------------------------------------------------------------------
-- The candidate `first` takes

first-inv : ∀ {X : Set} {m₁ m₂ : Maybe X} {v} → first m₁ m₂ ≡ just v
          → (m₁ ≡ just v) ⊎ (m₂ ≡ just v)
first-inv {m₁ = just x}  e = inj₁ e
first-inv {m₁ = nothing} e = inj₂ e

-- `first-inv`, with the two candidates read off the equation's type

private
  lastTwo : Term → TC (Term × Term)
  lastTwo t = reduce t >>= λ where
    (def _ as) → case reverse as of λ where
      (arg _ y ∷ arg _ x ∷ _) → pure (x , y)
      _                       → typeError (strErr "first-inv!: too few arguments" ∷ [])
    _          → typeError (strErr "first-inv!: not an application" ∷ [])

macro
  first-inv! : Term → Term → TC ⊤
  first-inv! e hole =
    inferType e >>= λ t → lastTwo t >>= λ where
      (l , _) → lastTwo l >>= λ where
        (m₁ , m₂) → unify hole (def (quote first-inv)
                                    (hArg unknown ∷ hArg m₁ ∷ hArg m₂ ∷ hArg unknown ∷ vArg e ∷ []))

------------------------------------------------------------------------
-- The unknowns free in `P`; a substitution fixing them fixes `P`

freeV : ∀ {Θ Φ} → Subst Θ Φ → Vars Φ
freeV P = vars (λ _ → true) (λ i → freeʳ i P) (λ i → freeᵉ i P)

fix-P : ∀ {Θ Φ} {P : Subst Θ Φ} {σ : Subst Φ Φ} → Fixes (freeV P) σ → (P ⨟ˢ σ) ≐ˢ P
fix-P {P = P} f = mk≐ˢ (λ α → fix-v f (sTy P α) (ty α)) (λ j → fix-r f (sR P j) (rr j))
                       (λ j → fix-e f (sE P j) (ee j))
  where
    ty : ∀ α → _ ⊆ᵛ freeV P
    ty α = mk⊆ᵛ (λ _ _ → refl)
                (λ i o → ∨-left _ _ (anyᶠ-intro (λ β → occʳ-v i (sTy P β)) α o))
                (λ i o → ∨-left _ _ (anyᶠ-intro (λ β → occᵉ-v i (sTy P β)) α o))

    rr : ∀ j → _ ⊆ᵛ freeV P
    rr j = mk⊆ᵛ (λ _ ())
                (λ i o → ∨-right (anyᶠ (λ β → occʳ-v i (sTy P β))) _
                                 (anyᶠ-intro (λ j' → occʳ-r i (sR P j')) j o))
                (λ i o → ∨-right (anyᶠ (λ β → occᵉ-v i (sTy P β))) _
                           (∨-left _ _ (anyᶠ-intro (λ j' → occᵉ-r i (sR P j')) j o)))

    ee : ∀ j → _ ⊆ᵛ freeV P
    ee j = mk⊆ᵛ (λ _ ()) (λ _ ())
                (λ i o → ∨-right (anyᶠ (λ β → occᵉ-v i (sTy P β))) _
                           (∨-right (anyᶠ (λ j' → occᵉ-r i (sR P j'))) _
                             (anyᶠ-intro (λ j' → occᵉ-e i (sE P j')) j o)))

fixes-⊆ : ∀ {Θ Θ' Φ} {P : Subst Θ Φ} {O : Subst Θ' Φ} {σ : Subst Φ Φ}
        → P ⊆ᶠ O → Fixes (freeV O) σ → Fixes (freeV P) σ
fixes-⊆ i f = mkFixes (fixᵗ f) (λ j p → fixʳ f j (⊆ʳ i p)) (λ j p → fixᵉ f j (⊆ᵉ i p))

-- An unknown free in no image of `O` is free in none of `P`

unfreeᵉ : ∀ {Θ Θ' Φ} {P : Subst Θ Φ} {O : Subst Θ' Φ} {k : EVar Φ}
        → P ⊆ᶠ O → freeᵉ k O ≡ false → freeᵉ k P ≡ false
unfreeᵉ {P = P} {k = k} i q with freeᵉ k P in e
... | false = refl
... | true  = ⊥-elim (t≢f (trans (sym (⊆ᵉ i e)) q))

unfreeʳ : ∀ {Θ Θ' Φ} {P : Subst Θ Φ} {O : Subst Θ' Φ} {k : RVar Φ}
        → P ⊆ᶠ O → freeʳ k O ≡ false → freeʳ k P ≡ false
unfreeʳ {P = P} {k = k} i q with freeʳ k P in e
... | false = refl
... | true  = ⊥-elim (t≢f (trans (sym (⊆ʳ i e)) q))

------------------------------------------------------------------------
-- Residuals moved by a substitution fixing `P`

module _ {Θ Φ} {P : Subst Θ Φ} where

  resinv-left : ∀ {σ : Subst Φ Φ} {R : Resid Φ} (D : Drops σ R) → ResInv P R → ResInv P (left D)
  resinv-left (drops Dʳ Dᵉ) r =
    mkResInv (inv-ss r) (λ m → I1′ʳ r (Unsettled.kept⊆ Dʳ m))
             (λ m → I1′ᵉ r (Unsettled.kept⊆ Dᵉ m)) (I5 r)

  -- given what the whole greater sides and the subtyping demands become

  resinv-move : ∀ {σ : Subst Φ Φ} {R : Resid Φ} → Fixes (freeV P) σ → ResInv P R
              → (∀ {x i} → (x , rvar i) ∈ rs R → Goodᵣ P (sR σ i))
              → (∀ {x i} → (x , evar i) ∈ es R → Goodₑ P (sE σ i))
              → (∀ {A B} → (A , B) ∈ ss R → TyGoodᵛ P (A [ σ ]ᵛ) × TyGoodᵛ P (B [ σ ]ᵛ))
              → ResInv P (R [ σ ]ᴿ)
  resinv-move {σ} {R} f r hr he hs = mkResInv sᵢ rᵢ eᵢ dᵢ
    where
      inc : (P ⨟ˢ σ) ⊆ᶠ P
      inc = ≐→⊆ᶠ (fix-P f)

      sᵢ : ∀ {A B} → (A , B) ∈ ss (R [ σ ]ᴿ) → TyGoodᵛ P A × TyGoodᵛ P B
      sᵢ m with ∈-map⁻ (mapᵖ (_[ σ ]ᵛ)) m
      ... | _ , m₀ , refl = hs m₀

      rᵢ : ∀ {x y} → (x , y) ∈ rs (R [ σ ]ᴿ) → Goodᵣ P y
      rᵢ m with ∈-map⁻ (mapᵖ (_[ σ ]ʳ)) m
      ... | (x₀ , y₀) , m₀ , refl with I1′ʳ r m₀
      ...   | whole i     = hr m₀
      ...   | outer {ρ} o = outer (outerᵣ-⊆ {ρ = ρ [ σ ]ʳ} inc (outerᵣ-⨟ P σ {ρ} o))

      eᵢ : ∀ {x y} → (x , y) ∈ es (R [ σ ]ᴿ) → Goodₑ P y
      eᵢ m with ∈-map⁻ (mapᵖ (_[ σ ]ᵉ)) m
      ... | (x₀ , y₀) , m₀ , refl with I1′ᵉ r m₀
      ...   | whole i     = he m₀
      ...   | outer {ε} o = outer (outerₑ-⊆ {ε = ε [ σ ]ᵉ} inc (outerₑ-⨟ P σ {ε} o))

      dᵢ : ∀ {E} → E ∈ dfs (R [ σ ]ᴿ) → Great P E
      dᵢ m with ∈-map⁻ (_[ σ ]ᵈ) m
      ... | E₀ , m₀ , refl = great-⊆ inc (E₀ [ σ ]ᵈ) (great-⨟ P σ E₀ (I5 r m₀))

  -- by a good substitution

  resinv-gv : ∀ {σ : Subst Φ Φ} {R : Resid Φ} → Fixes (freeV P) σ → GV (P ⨟ˢ σ) σ
            → ResInv P R → ResInv P (R [ σ ]ᴿ)
  resinv-gv f g r = resinv-≐ (fix-P f) (resinv-subst {P = P} g r)

------------------------------------------------------------------------
-- Settled and normal forms

-- An entry a test keeps fails the test

dropping-kept : ∀ {Ψ} {X : Set} {Pr : ∀ {Ψ'} → Hyps Ψ' → Subst Ψ Ψ' → X → Set}
              → (d : X → 𝔹) → (l : List X) → (h : ∀ {a} → a ∈ l → d a ≡ true → Every Pr a)
              → ∀ {a} → a ∈ Unsettled.kept (dropping d l h) → d a ≡ false
dropping-kept d (a ∷ l) h m with d a in q | h (here refl)
... | true  | _ = dropping-kept d l (λ m' → h (there m')) m
... | false | _ with m
...   | here refl = q
...   | there m'  = dropping-kept d l (λ m' → h (there m')) m'

-- A refined disjunction bounds its grade by the unit

refine-ords : ∀ {Ψ} (l : List (OVType Ψ × RExp Ψ)) {x y}
            → (x , y) ∈ Refined.ords (refine l) → y ≡ ûᵣ
refine-ords l m = PROBE
  where postulate PROBE : _

module _ {Θ₀ Θ Φ} {P : Subst Θ₀ Φ} {O : Subst (Θ +e) Φ} {R₀ : Resid Φ} where

  resinv-settle : (L : Localised O R₀) → ResInv P (lR L) → ResInv P (lR (loc-settle L))
  resinv-settle L r = mkResInv (inv-ss r) rᵢ eᵢ (I5 r)
    where
      Uʳ = unsettled settledʳ (rs (lR L))
      Uᵉ = unsettled settledᵉ (es (lR L))

      rᵢ : ∀ {x y} → (x , y) ∈ rs (lR (loc-settle L)) → Goodᵣ P y
      rᵢ m with ∈-++⁻ (Unsettled.kept Uʳ) m
      ... | inj₁ mk = I1′ʳ r (Unsettled.kept⊆ Uʳ mk)
      ... | inj₂ mo = subst (Goodᵣ P) (sym (refine-ords (Unsettled.kept (unsettled settledᵈ (ds (lR L)))) mo)) (outer ((λ ()) , (λ ())))

      eᵢ : ∀ {x y} → (x , y) ∈ es (lR (loc-settle L)) → Goodₑ P y
      eᵢ m = I1′ᵉ r (Unsettled.kept⊆ Uᵉ m)

  resinv-norm : (L : Localised O R₀) → ResInv P (lR L) → ResInv P (lR (loc-normal L))
  resinv-norm L r = resinv-normal {R = lR L} r

------------------------------------------------------------------------
-- Identifying the unknowns of a component: a renaming fixing `O`

collapse-fixes : ∀ {Θ Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ)
               → Fixes (freeV O) (Collapse.cσ (collapse O R))
collapse-fixes O R = mkFixes (λ _ _ → refl) fr fe
  where
    fr : ∀ i → freeʳ i O ≡ true → sR (Collapse.cσ (collapse O R)) i ≡ rvar i
    fr i o = [ cong rvar , (λ mv → ⊥-elim (t≢f (trans (sym o) (proj₁ mv)))) ]′
               (Cʳ.stays O R (Cʳ.moves O R (edgesʳ (rs R))) i)

    fe : ∀ i → freeᵉ i O ≡ true → sE (Collapse.cσ (collapse O R)) i ≡ evar i
    fe i o = [ cong evar , (λ mv → ⊥-elim (t≢f (trans (sym o) (proj₁ mv)))) ]′
               (Cᵉ.stays O R (Cᵉ.moves O R (edgesᵉ (es R))) i)

collapse-gv : ∀ {Θ Θ' Φ} {X : Subst Θ' Φ} (O : Subst (Θ +e) Φ) (R : Resid Φ)
            → GV X (Collapse.cσ (collapse O R))
collapse-gv O R = GV-ren (λ α → α , refl) (λ i → _ , refl) (λ i → _ , refl)

------------------------------------------------------------------------
-- Sending a set to the top: members are free in no image of `O`

private
  topE-hit : ∀ {Φ} {k : EVar Φ} (b : 𝔹) (i : EVar Φ) → occᵉ-e k (topE b i) ≡ true → (b ≡ false) × (k ≡ i)
  topE-hit {k = k} false i q = refl , true-dec (k ≟ᶠ i) q

  topR-hit : ∀ {Φ} {k : RVar Φ} (b : 𝔹) (i : RVar Φ) → occʳ-r k (topR b i) ≡ true → (b ≡ false) × (k ≡ i)
  topR-hit {k = k} false i q = refl , true-dec (k ≟ᶠ i) q

  topR-occᵉ : ∀ {Φ} {k : EVar Φ} (b : 𝔹) (i : RVar Φ) → occᵉ-r k (topR b i) ≡ false
  topR-occᵉ true  i = refl
  topR-occᵉ false i = refl

tops-fixes : ∀ {Θ Φ} (O : Subst Θ Φ) (l : List (Mem Φ)) → freeᴹ l O ≡ false
           → Fixes (freeV O) (tops l)
tops-fixes O l fx = mkFixes (λ _ _ → refl) fr fe
  where
    eq = freeᴹ-fix l O fx

    fr : ∀ k → freeʳ k O ≡ true → sR (tops l) k ≡ rvar k
    fr k o with freeʳ-⨟⁻ O (tops l) (trans (freeʳ-≐ eq k) o)
    ... | inj₂ (i , p , q) with topR-hit (inᴿ i l) i q
    ...   | f , refl = cong (λ b → topR b k) f

    fe : ∀ k → freeᵉ k O ≡ true → sE (tops l) k ≡ evar k
    fe k o with freeᵉ-⨟⁻ O (tops l) (trans (freeᵉ-≐ eq k) o)
    ... | inj₂ (inj₁ (i , p , q)) = ⊥-elim (t≢f (trans (sym q) (topR-occᵉ (inᴿ i l) i)))
    ... | inj₂ (inj₂ (i , p , q)) with topE-hit (inᴱ i l) i q
    ...   | f , refl = cong (λ b → topE b k) f

tops-gv : ∀ {Θ Φ} {X : Subst Θ Φ} {l : List (Mem Φ)} → GV X (tops l)
tops-gv {X = X} {l} = mkGV (λ α → tt) rr ee
  where
    rr : ∀ j → Goodᵣ X (sR (tops l) j)
    rr j with inᴿ j l
    ... | true  = outer ((λ ()) , (λ ()))
    ... | false = whole j

    ee : ∀ j → Goodₑ X (sE (tops l) j)
    ee j with inᴱ j l
    ... | true  = outer (λ ())
    ... | false = whole j

------------------------------------------------------------------------
-- The steps, at a scope entered with `O`

module Steps {Θ₀ Θ Φ} (O : Subst (Θ +e) Φ) (P : Subst Θ₀ Φ) (inc : P ⊆ᶠ O) where

  -- the value of a step, wherever its unknown is a whole greater side
  -- left open

  ValE : EVar Φ → EExp Φ → Resid Φ → Set
  ValE k b R = ∀ {x} → (x , evar k) ∈ es R → Goodₑ P b

  ValR : RVar Φ → RExp Φ → Resid Φ → Set
  ValR k b R = ∀ {x} → (x , rvar k) ∈ rs R → Goodᵣ P b

  stepᵉ-val : ∀ {k R b} {st : Keeps (updᵉ k b) R} {dr : Drops (updᵉ k b) R}
            → ResInv P R → stepᵉ k R ≡ just (b , st , dr) → Cleanᵉ k R × ValE k b (left dr)
  stepᵉ-val {k} {R} r e with cleanᵉ? k R
  ... | nothing = ⊥-elim (nothing≢just e)
  ... | just cl
    with Bᵉ.lowsOf {Φ} k (es R) | Bᵉʳ.freeRs {Φ} k (rs R) | Bᵉ.upsOf {Φ} k (es R)
       | Bᵉʳ.freeLs {Φ} k (rs R) | dfreeᵉ? k R | Is-just? uₑ-least? | occursᵉ k R
       | Bᵉ.freeLs {Φ} k (es R) | occursᵉ⁺ k R
  ...   | ml | mf | mu | mfl | mdf | mi | o | mfe | o⁺ with first-inv! e
  -- lowering drops each ordering with `k` on its greater side
  stepᵉ-val r e | just cl | nothing | _ | _ | _ | _ | _ | _ | _ | _ | inj₁ e₁ = ⊥-elim (nothing≢just e₁)
  stepᵉ-val r e | just cl | just (Bᵉ.lows [] _ _ _ _ _ _) | _ | _ | _ | _ | _ | _ | _ | _ | inj₁ e₁ =
    ⊥-elim (nothing≢just e₁)
  stepᵉ-val r e | just cl | just (Bᵉ.lows (_ ∷ _) _ _ _ _ _ _) | nothing | _ | _ | _ | _ | _ | _ | _
            | inj₁ e₁ = ⊥-elim (nothing≢just e₁)
  stepᵉ-val {k} {R} r e | just cl | just (Bᵉ.lows (x ∷ xs) _ _ _ _ _ _) | just fr | _ | _ | _ | _ | _
            | _ | _ | inj₁ e₁ with stills? dir↓ (updᵉ k (joinₑ x xs)) (dfs R)
  ... | nothing = ⊥-elim (nothing≢just e₁)
  ... | just sd with e₁
  ...   | refl = cl , λ m → ⊥-elim (t≢f (trans (sym (≟-self k)) (dropping-kept _ (es R) _ m)))
  stepᵉ-val r e | just cl | ml | mf | mu | mfl | mdf | mi | o | mfe | o⁺ | inj₂ e₂ with first-inv! e₂
  -- raising, to a greater side
  stepᵉ-val r e | just cl | _ | _ | nothing | _ | _ | _ | _ | _ | _ | inj₂ e₂ | inj₁ e₃ =
    ⊥-elim (nothing≢just e₃)
  stepᵉ-val r e | just cl | _ | _ | just _ | nothing | _ | _ | _ | _ | _ | inj₂ e₂ | inj₁ e₃ =
    ⊥-elim (nothing≢just e₃)
  stepᵉ-val r e | just cl | _ | _ | just _ | just _ | nothing | _ | _ | _ | _ | inj₂ e₂ | inj₁ e₃ =
    ⊥-elim (nothing≢just e₃)
  stepᵉ-val {k} {R} r e | just cl | _ | _ | just up | just _ | just _ | _ | _ | _ | _ | inj₂ e₂
            | inj₁ e₃ with stills? dir↑ (updᵉ k (Bᵉ.cap up)) (dfs R)
  ... | nothing = ⊥-elim (nothing≢just e₃)
  ... | just sd with e₃
  ...   | refl = cl , λ _ → I1′ᵉ r (Bᵉ.srcᵘ up)
  stepᵉ-val r e | just cl | ml | mf | mu | mfl | mdf | mi | o | mfe | o⁺ | inj₂ e₂ | inj₂ e₄
    with first-inv! e₄
  -- the unit
  stepᵉ-val r e | just cl | _ | _ | _ | _ | _ | nothing | _ | _ | _ | inj₂ e₂ | inj₂ e₄ | inj₁ e₅ =
    ⊥-elim (nothing≢just e₅)
  stepᵉ-val r e | just cl | nothing | _ | _ | _ | _ | just _ | _ | _ | _ | inj₂ e₂ | inj₂ e₄ | inj₁ e₅ =
    ⊥-elim (nothing≢just e₅)
  stepᵉ-val r e | just cl | just (Bᵉ.lows (_ ∷ _) _ _ _ _ _ _) | _ | _ | _ | _ | just _ | _ | _ | _
            | inj₂ e₂ | inj₂ e₄ | inj₁ e₅ = ⊥-elim (nothing≢just e₅)
  stepᵉ-val r e | just cl | just (Bᵉ.lows [] _ _ _ _ _ _) | nothing | _ | _ | _ | just _ | _ | _ | _
            | inj₂ e₂ | inj₂ e₄ | inj₁ e₅ = ⊥-elim (nothing≢just e₅)
  stepᵉ-val r e | just cl | just (Bᵉ.lows [] _ _ _ _ _ _) | just _ | _ | _ | _ | just _ | false | _ | _
            | inj₂ e₂ | inj₂ e₄ | inj₁ e₅ = ⊥-elim (nothing≢just e₅)
  stepᵉ-val {k} {R} r e | just cl | just (Bᵉ.lows [] _ _ _ _ _ _) | just _ | _ | _ | _ | just _ | true
            | _ | _ | inj₂ e₂ | inj₂ e₄ | inj₁ e₅ with stills? dir↓ (updᵉ k ûₑ) (dfs R)
  ... | nothing = ⊥-elim (nothing≢just e₅)
  ... | just sd with e₅
  ...   | refl = cl , λ _ → outer (λ ())
  -- the top
  stepᵉ-val r e | just cl | _ | _ | _ | _ | _ | _ | _ | nothing | _ | inj₂ e₂ | inj₂ e₄ | inj₂ e₆ =
    ⊥-elim (nothing≢just e₆)
  stepᵉ-val r e | just cl | _ | _ | _ | nothing | _ | _ | _ | just _ | _ | inj₂ e₂ | inj₂ e₄ | inj₂ e₆ =
    ⊥-elim (nothing≢just e₆)
  stepᵉ-val r e | just cl | _ | _ | _ | just _ | nothing | _ | _ | just _ | _ | inj₂ e₂ | inj₂ e₄
            | inj₂ e₆ = ⊥-elim (nothing≢just e₆)
  stepᵉ-val r e | just cl | _ | _ | _ | just _ | just _ | _ | _ | just _ | false | inj₂ e₂ | inj₂ e₄
            | inj₂ e₆ = ⊥-elim (nothing≢just e₆)
  stepᵉ-val {k} {R} r e | just cl | _ | _ | _ | just _ | just _ | _ | _ | just _ | true | inj₂ e₂
            | inj₂ e₄ | inj₂ e₆ with stills? dir↑ (updᵉ k (econst ⊤ₑ)) (dfs R)
  ... | nothing = ⊥-elim (nothing≢just e₆)
  ... | just sd with e₆
  ...   | refl = cl , λ _ → outer (λ ())

  stepʳ-val : ∀ {k R b} {st : Keeps (updʳ k b) R} {dr : Drops (updʳ k b) R}
            → ResInv P R → stepʳ k R ≡ just (b , st , dr) → Cleanʳ k R × ValR k b (left dr)
  stepʳ-val {k} {R} r e with cleanʳ? k R
  ... | nothing = ⊥-elim (nothing≢just e)
  ... | just cl
    with Bʳ.lowsOf {Φ} k (rs R) | Bʳ.upsOf {Φ} k (rs R) | dfreeʳ? k R | Is-just? uᵣ-least?
       | occursʳ k R | Bʳ.freeLs {Φ} k (rs R) | occursʳ⁺ k R
  ...   | ml | mu | mdf | mi | o | mfl | o⁺ with first-inv! e
  stepʳ-val r e | just cl | nothing | _ | _ | _ | _ | _ | _ | inj₁ e₁ = ⊥-elim (nothing≢just e₁)
  stepʳ-val r e | just cl | just (Bʳ.lows [] _ _ _ _ _ _) | _ | _ | _ | _ | _ | _ | inj₁ e₁ =
    ⊥-elim (nothing≢just e₁)
  stepʳ-val {k} {R} r e | just cl | just (Bʳ.lows (x ∷ xs) _ _ _ _ _ _) | _ | _ | _ | _ | _ | _
            | inj₁ e₁ with stills? dir↓ (updʳ k (joinᵣ x xs)) (dfs R)
  ... | nothing = ⊥-elim (nothing≢just e₁)
  ... | just sd with e₁
  ...   | refl = cl , λ m → ⊥-elim (t≢f (trans (sym (≟-self k)) (dropping-kept _ (rs R) _ m)))
  stepʳ-val r e | just cl | ml | mu | mdf | mi | o | mfl | o⁺ | inj₂ e₂ with first-inv! e₂
  stepʳ-val r e | just cl | _ | nothing | _ | _ | _ | _ | _ | inj₂ e₂ | inj₁ e₃ = ⊥-elim (nothing≢just e₃)
  stepʳ-val r e | just cl | _ | just _ | nothing | _ | _ | _ | _ | inj₂ e₂ | inj₁ e₃ =
    ⊥-elim (nothing≢just e₃)
  stepʳ-val {k} {R} r e | just cl | _ | just up | just _ | _ | _ | _ | _ | inj₂ e₂ | inj₁ e₃
    with stills? dir↑ (updʳ k (Bʳ.cap up)) (dfs R)
  ... | nothing = ⊥-elim (nothing≢just e₃)
  ... | just sd with e₃
  ...   | refl = cl , λ _ → I1′ʳ r (Bʳ.srcᵘ up)
  stepʳ-val r e | just cl | ml | mu | mdf | mi | o | mfl | o⁺ | inj₂ e₂ | inj₂ e₄ with first-inv! e₄
  stepʳ-val r e | just cl | _ | _ | _ | nothing | _ | _ | _ | inj₂ e₂ | inj₂ e₄ | inj₁ e₅ =
    ⊥-elim (nothing≢just e₅)
  stepʳ-val r e | just cl | nothing | _ | _ | just _ | _ | _ | _ | inj₂ e₂ | inj₂ e₄ | inj₁ e₅ =
    ⊥-elim (nothing≢just e₅)
  stepʳ-val r e | just cl | just (Bʳ.lows (_ ∷ _) _ _ _ _ _ _) | _ | _ | just _ | _ | _ | _ | inj₂ e₂
            | inj₂ e₄ | inj₁ e₅ = ⊥-elim (nothing≢just e₅)
  stepʳ-val r e | just cl | just (Bʳ.lows [] _ _ _ _ _ _) | _ | _ | just _ | false | _ | _ | inj₂ e₂
            | inj₂ e₄ | inj₁ e₅ = ⊥-elim (nothing≢just e₅)
  stepʳ-val {k} {R} r e | just cl | just (Bʳ.lows [] _ _ _ _ _ _) | _ | _ | just _ | true | _ | _
            | inj₂ e₂ | inj₂ e₄ | inj₁ e₅ with stills? dir↓ (updʳ k ûᵣ) (dfs R)
  ... | nothing = ⊥-elim (nothing≢just e₅)
  ... | just sd with e₅
  ...   | refl = cl , λ _ → outer ((λ ()) , (λ ()))
  stepʳ-val r e | just cl | _ | _ | _ | _ | _ | nothing | _ | inj₂ e₂ | inj₂ e₄ | inj₂ e₆ =
    ⊥-elim (nothing≢just e₆)
  stepʳ-val r e | just cl | _ | _ | nothing | _ | _ | just _ | _ | inj₂ e₂ | inj₂ e₄ | inj₂ e₆ =
    ⊥-elim (nothing≢just e₆)
  stepʳ-val r e | just cl | _ | _ | just _ | _ | _ | just _ | false | inj₂ e₂ | inj₂ e₄ | inj₂ e₆ =
    ⊥-elim (nothing≢just e₆)
  stepʳ-val {k} {R} r e | just cl | _ | _ | just _ | _ | _ | just _ | true | inj₂ e₂ | inj₂ e₄
            | inj₂ e₆ with stills? dir↑ (updʳ k (rconst ⊤ᵣ)) (dfs R)
  ... | nothing = ⊥-elim (nothing≢just e₆)
  ... | just sd with e₆
  ...   | refl = cl , λ _ → outer ((λ ()) , (λ ()))

  -- each step keeps the invariant

  stepᵉ-inv : ∀ {k} → freeᵉ k O ≡ false
            → ∀ {R b} {st : Keeps (updᵉ k b) R} {dr : Drops (updᵉ k b) R}
            → ResInv P R → stepᵉ k R ≡ just (b , st , dr) → ResInv P (left dr [ updᵉ k b ]ᴿ)
  stepᵉ-inv {k} lk {R} {b} {dr = dr} r e with stepᵉ-val r e
  ... | cl , v = resinv-move (fixes-updᵉ k b (unfreeᵉ inc lk)) (resinv-left dr r)
                             (λ {_} {i} _ → whole i) wₑ wₛ
    where
      wₑ : ∀ {x i} → (x , evar i) ∈ es (left dr) → Goodₑ P (sE (updᵉ k b) i)
      wₑ {i = i} m with i ≟ᶠ k
      ... | yes refl = v m
      ... | no _     = whole i

      wₛ : ∀ {A B} → (A , B) ∈ ss R → TyGoodᵛ P (A [ updᵉ k b ]ᵛ) × TyGoodᵛ P (B [ updᵉ k b ]ᵛ)
      wₛ {A} {B} m with ∨-false (occᵉ-v k A) (occᵉ-v k B) (Cleanᵉ.css cl m)
      ... | qA , qB = subst (TyGoodᵛ P) (sym (updᵉ-v k b A qA)) (proj₁ (inv-ss r m)) ,
                      subst (TyGoodᵛ P) (sym (updᵉ-v k b B qB)) (proj₂ (inv-ss r m))

  stepʳ-inv : ∀ {k} → freeʳ k O ≡ false
            → ∀ {R b} {st : Keeps (updʳ k b) R} {dr : Drops (updʳ k b) R}
            → ResInv P R → stepʳ k R ≡ just (b , st , dr) → ResInv P (left dr [ updʳ k b ]ᴿ)
  stepʳ-inv {k} lk {R} {b} {dr = dr} r e with stepʳ-val r e
  ... | cl , v = resinv-move (fixes-updʳ k b (unfreeʳ inc lk)) (resinv-left dr r)
                             wᵣ (λ {_} {i} _ → whole i) wₛ
    where
      wᵣ : ∀ {x i} → (x , rvar i) ∈ rs (left dr) → Goodᵣ P (sR (updʳ k b) i)
      wᵣ {i = i} m with i ≟ᶠ k
      ... | yes refl = v m
      ... | no _     = whole i

      wₛ : ∀ {A B} → (A , B) ∈ ss R → TyGoodᵛ P (A [ updʳ k b ]ᵛ) × TyGoodᵛ P (B [ updʳ k b ]ᵛ)
      wₛ {A} {B} m with ∨-false (occʳ-v k A) (occʳ-v k B) (Cleanʳ.css cl m)
      ... | qA , qB = subst (TyGoodᵛ P) (sym (updʳ-v k b A qA)) (proj₁ (inv-ss r m)) ,
                      subst (TyGoodᵛ P) (sym (updʳ-v k b B qB)) (proj₂ (inv-ss r m))

  -- the stages of a round

  module _ {R₀ : Resid Φ} where

    passᵉ-inv : ∀ ks (L : Localised O R₀) → ResInv P (lR L) → ResInv P (lR (proj₁ (passᵉ O R₀ ks L)))
    passᵉ-inv []             L r = r
    passᵉ-inv ((k , q) ∷ ks) L r with stepᵉ k (lR L) in e
    ... | nothing            = passᵉ-inv ks L r
    ... | just (b , st , dr) = passᵉ-inv ks _ (stepᵉ-inv q r e)

    passʳ-inv : ∀ ks (L : Localised O R₀) → ResInv P (lR L) → ResInv P (lR (proj₁ (passʳ O R₀ ks L)))
    passʳ-inv []             L r = r
    passʳ-inv ((k , q) ∷ ks) L r with stepʳ k (lR L) in e
    ... | nothing            = passʳ-inv ks L r
    ... | just (b , st , dr) = passʳ-inv ks _ (stepʳ-inv q r e)

    collapseL-inv : ∀ (L : Localised O R₀) → ResInv P (lR L) → ResInv P (lR (proj₁ (collapseL O R₀ L)))
    collapseL-inv L r with Collapse.cmove (collapse O (lR L))
    ... | false = r
    ... | true  = resinv-gv {P = P} (fixes-⊆ inc (collapse-fixes O (lR L))) (collapse-gv O (lR L))
                            (resinv-left keepAll r)

    raiseL-inv : ∀ (L : Localised O R₀) {L'} → raiseL O R₀ L ≡ just L' → ResInv P (lR L)
               → ResInv P (lR L')
    raiseL-inv L e r with evar? (sE O (newᵉ {Θ}))
    ... | nothing = ⊥-elim (nothing≢just e)
    ... | just (j , eqj) with Find.raise? O (lR L) j
    ...   | nothing = ⊥-elim (nothing≢just e)
    ...   | just (raised l rc ue ur cl sd fx) with e
    ...     | refl = resinv-gv {P = P} (fixes-⊆ inc (tops-fixes O l fx)) (tops-gv {l = l})
                              (resinv-left keepAll r)

    rounds-inv : ∀ n (L : Localised O R₀) → ResInv P (lR L) → ResInv P (lR (rounds O R₀ n L))
    rounds-inv nzero    L r = r
    rounds-inv (nsuc n) L r with joined (lR L)
    ... | true  with collapseL O R₀ (loc-settle (loc-normal L))
                   | collapseL-inv (loc-settle (loc-normal L))
                       (resinv-settle (loc-normal L) (resinv-norm L r))
    ...   | L₁ , c₁ | r₁ with passᵉ O R₀ (misses (λ k → freeᵉ k O)) L₁
                            | passᵉ-inv (misses (λ k → freeᵉ k O)) L₁ r₁
    ...     | L₂ , c₂ | r₂ with passʳ O R₀ (misses (λ k → freeʳ k O)) L₂
                              | passʳ-inv (misses (λ k → freeʳ k O)) L₂ r₂
    ...       | L₃ , c₃ | r₃ with (c₁ ∨ c₂) ∨ c₃
    ...         | true  = rounds-inv n (loc-settle L₃) (resinv-settle L₃ r₃)
    ...         | false with raiseL O R₀ L₃ in e
    ...           | just L₄ = rounds-inv n (loc-settle L₄) (resinv-settle L₄ (raiseL-inv L₃ e r₃))
    ...           | nothing = r₃
    rounds-inv (nsuc n) L r | false with collapseL O R₀ (loc-normal L)
                                       | collapseL-inv (loc-normal L) (resinv-norm L r)
    ...   | L₁ , c₁ | r₁ with passᵉ O R₀ (misses (λ k → freeᵉ k O)) L₁
                            | passᵉ-inv (misses (λ k → freeᵉ k O)) L₁ r₁
    ...     | L₂ , c₂ | r₂ with passʳ O R₀ (misses (λ k → freeʳ k O)) L₂
                              | passʳ-inv (misses (λ k → freeʳ k O)) L₂ r₂
    ...       | L₃ , c₃ | r₃ with (c₁ ∨ c₂) ∨ c₃
    ...         | true  = rounds-inv n (loc-settle L₃) (resinv-settle L₃ r₃)
    ...         | false with raiseL O R₀ L₃ in e
    ...           | just L₄ = rounds-inv n (loc-settle L₄) (resinv-settle L₄ (raiseL-inv L₃ e r₃))
    ...           | nothing = r₃

------------------------------------------------------------------------
-- `localise` keeps the invariant against the unknowns the scope was
-- entered with

localise-good : ∀ {Θ₀ Θ Φ} → (O : Subst (Θ +e) Φ) → (P : Subst Θ₀ Φ) → (R : Resid Φ)
              → P ⊆ᶠ O → ResInv P R → ResInv P (lR (localise O R))
localise-good {Φ = Φ} O P R inc r =
  resinv-settle (rounds (memo O) R (nE Φ + nR Φ) (loc-settle L₀))
    (rounds-inv (nE Φ + nR Φ) (loc-settle L₀) (resinv-settle L₀ r))
  where
    open Steps (memo O) P (⊆ᶠ-trans inc (≐→⊆ᶠ (≐ˢ-sym (memo-≐ O))))

    L₀ : Localised (memo O) R
    L₀ = loc-id
