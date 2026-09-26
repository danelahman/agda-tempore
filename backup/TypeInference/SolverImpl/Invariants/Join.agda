------------------------------------------------------------------
-- The decider finds an expression below a join of it and others  --
--                                                                --
-- Every alternative of the smaller side is an alternative of the --
-- join's normal form, or that normal form is the top. Grouping   --
-- and folding it puts each alternative below one of the folded   --
-- sum, slot by slot, and the product search then matches the two --
-- atom by atom, passing over a unit slot on either side; the top --
-- absorbs every atom.                                            --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Base using (_<∣>_)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to isJust)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; +-suc; ≤-pred)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Invariants.Join (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Hyps   S

open import TypeInference.SolverImpl.Normal S
open import TypeInference.SolverImpl.Eliminate S using (joinₑ; joinᵣ)
open import TypeInference.SolverImpl.Invariants.Sums S
open import TypeInference.SolverImpl.Invariants.Flat S

------------------------------------------------------------------------
-- Alternatives

<∣>-l : ∀ {A : Set} {m₁ m₂ : Maybe A} → Is-just m₁ → Is-just (m₁ <∣> m₂)
<∣>-l {m₁ = just _} _ = isJust tt

<∣>-r : ∀ {A : Set} {m₁ m₂ : Maybe A} → Is-just m₂ → Is-just (m₁ <∣> m₂)
<∣>-r {m₁ = just _}  _ = isJust tt
<∣>-r {m₁ = nothing} j = j

-- fuel

step≤ : ∀ {m n k} → suc (m + suc n) ≤ suc k → m + n ≤ k
step≤ {m} {n} {k} p = ≤-trans (n≤1+n (m + n)) (subst (_≤ k) (+-suc m n) (≤-pred p))

stepʳ≤ : ∀ {m n k} → m + suc n ≤ suc k → m + n ≤ k
stepʳ≤ {m} {n} {k} p = ≤-pred (subst (_≤ suc k) (+-suc m n) p)

------------------------------------------------------------------------
-- Effect grades

module GEₑ {Θ : Scope} =
  Groups {EExp Θ} {E} {EVar Θ} _≡̂ₑ_ ≡̂ₑ-refl ≡̂ₑ-sym ≡̂ₑ-trans _·̂ₑ_ _⊔̂ₑ_
         ≡̂ₑ-cong ≡̂ₑ-cong-⊔ ≡̂ₑ-idem-⊔ ≡̂ₑ-comm-⊔ ≡̂ₑ-assoc-⊔
         ≡̂ₑ-distribˡ-⊔ ≡̂ₑ-distribʳ-⊔
         econst _⊔ₑ_ ≡̂ₑ-const-⊔ _≡ₑ?_ evar _≟ᶠ_ (_<ᵉᵛ_ {Θ})

module BEₑ {Θ : Scope} = GEₑ.Below {Θ} _≾ₑ_ ≾ₑ-refl ≾ₑ-trans ⊔ₑ-ubˡ ⊔ₑ-ubʳ

open BEₑ using (_≤ˢ_; _≤ᵖ_; ≤⌜⌝; ≤▸; ≤ᵖ-at; canonical-≤)

module _ {Θ} {Q : Hyps Θ} where

  open Searchₑ {Θ} {Q} (tableₑ Q)

  link-cₑ : ∀ {c d} → c ≾ₑ d → Is-just (linkₑ? {Q = Q} (ac c) (ac d))
  link-cₑ {c} {d} p with c ≾ₑ? d
  ... | yes _ = isJust tt
  ... | no ¬p = ⊥-elim (¬p p)

  link-vₑ : ∀ i → Is-just (linkₑ? {Q = Q} (av i) (av i))
  link-vₑ i with i ≟ᶠ i
  ... | yes refl = isJust tt
  ... | no ¬p    = ⊥-elim (¬p refl)

  reach-linkₑ : ∀ {a b} → Is-just (linkₑ? {Q = Q} a b) → Is-just (reachₑ? a b)
  reach-linkₑ j = <∣>-l j

  atom-linkₑ : ∀ {a b} → Is-just (linkₑ? {Q = Q} a b) → Is-just (atom≾ₑ a b)
  atom-linkₑ j = <∣>-l j

  ceil-topₑ : ∀ {ε d} → ⊤ₑ ≾ₑ d → Is-just (ceilₑ {ε} (ac d))
  ceil-topₑ {d = d} p with reachₑ? (ac ⊤ₑ) (ac d) | reach-linkₑ {ac ⊤ₑ} {ac d} (link-cₑ p)
  ... | just _  | _  = isJust tt
  ... | nothing | ()

  unit-cₑ : ∀ {d} → uₑ ≾ₑ d → Is-just (unit≾ₑ (ac d))
  unit-cₑ p = <∣>-r {m₁ = min≾ₑ (Is-just? uₑ-least?)} (atom-linkₑ (link-cₑ p))

  ≾unit-cₑ : ∀ {c} → c ≾ₑ uₑ → Is-just (≾unitₑ (ac c))
  ≾unit-cₑ p = atom-linkₑ (link-cₑ p)

  ≾unit-topₑ : ∀ a → ⊤ₑ ≾ₑ uₑ → Is-just (≾unitₑ a)
  ≾unit-topₑ a p = <∣>-r {m₁ = linkₑ? a (ac uₑ)} (<∣>-l (ceil-topₑ p))

  -- one step of the product search

  match-just : ∀ {ε ε'} a b {r : Maybe (Q ⊩ ε ≾̂ₑ ε')} → Is-just (atom≾ₑ a b) → Is-just r
             → Is-just (matchₑ a b r)
  match-just a b {r} ja jr with atom≾ₑ a b | ja
  ... | just _ | _ with r | jr
  ...   | just _ | _ = isJust tt

  skipʳ-just : ∀ {ε ε'} b {r : Maybe (Q ⊩ ε ≾̂ₑ ε')} → Is-just (unit≾ₑ b) → Is-just r
             → Is-just (skipʳₑ b r)
  skipʳ-just b {r} ja jr with unit≾ₑ b | ja
  ... | just _ | _ with r | jr
  ...   | just _ | _ = isJust tt

  skipˡ-just : ∀ {ε ε'} a {r : Maybe (Q ⊩ ε ≾̂ₑ ε')} → Is-just (≾unitₑ a) → Is-just r
             → Is-just (skipˡₑ a r)
  skipˡ-just a {r} ja jr with ≾unitₑ a | ja
  ... | just _ | _ with r | jr
  ...   | just _ | _ = isJust tt

  intoTop-just : ∀ {ε ε'} a b {r : Maybe (Q ⊩ ε ≾̂ₑ ⟦ b ⟧ᵉᵃ ·̂ₑ ε')} → Is-just (absorbs≾ₑ a b)
               → Is-just r → Is-just (intoTopₑ a b r)
  intoTop-just a b {r} ja jr with absorbs≾ₑ a b | ja
  ... | just _ | _ with r | jr
  ...   | just _ | _ = isJust tt

  -- the searches, given what their first test finds

  data Dom : List (EAtom Θ) → List (EAtom Θ) → Set where
    d[]    : Dom [] []
    dmatch : ∀ {a b as bs} → Is-just (atom≾ₑ a b) → Dom as bs → Dom (a ∷ as) (b ∷ bs)
    dskipʳ : ∀ {as b bs} → Is-just (unit≾ₑ b) → Dom as bs → Dom as (b ∷ bs)
    dskipˡ : ∀ {a as bs} → Is-just (≾unitₑ a) → Dom as bs → Dom (a ∷ as) bs
    dtop   : ∀ {a as b bs} → Is-just (absorbs≾ₑ a b) → Dom as (b ∷ bs) → Dom (a ∷ as) (b ∷ bs)

  dom-prodˢ : ∀ {as bs} → Dom as bs → ∀ n → length as + length bs ≤ n → Is-just (prodˢ≾ₑ n as bs)
  dom-prodˢ d[] n p = isJust tt
  dom-prodˢ (dmatch {a} {b} {as} {bs} j d) (suc n) p =
    <∣>-l (match-just a b j (dom-prodˢ d n (step≤ {length as} p)))
  dom-prodˢ (dskipʳ {[]} {b} {bs} j d) (suc n) p =
    <∣>-l (skipʳ-just b j (dom-prodˢ d n (≤-pred p)))
  dom-prodˢ (dskipʳ {a ∷ as} {b} {bs} j d) (suc n) p =
    <∣>-r {m₁ = matchₑ a b (prodˢ≾ₑ n as bs)}
      (<∣>-l (skipʳ-just b j (dom-prodˢ d n (stepʳ≤ {length (a ∷ as)} p))))
  dom-prodˢ (dskipˡ {a} {as} {[]} j d) (suc n) p =
    <∣>-l (skipˡ-just a j (dom-prodˢ d n (≤-pred p)))
  dom-prodˢ (dskipˡ {a} {as} {b ∷ bs} j d) (suc n) p =
    <∣>-r {m₁ = matchₑ a b (prodˢ≾ₑ n as bs)}
      (<∣>-r {m₁ = skipʳₑ b (prodˢ≾ₑ n (a ∷ as) bs)}
        (<∣>-l (skipˡ-just a j (dom-prodˢ d n (≤-pred p)))))
  dom-prodˢ (dtop {a} {as} {b} {bs} j d) (suc n) p =
    <∣>-r {m₁ = matchₑ a b (prodˢ≾ₑ n as bs)}
      (<∣>-r {m₁ = skipʳₑ b (prodˢ≾ₑ n (a ∷ as) bs)}
        (<∣>-r {m₁ = skipˡₑ a (prodˢ≾ₑ n as (b ∷ bs))}
          (<∣>-l (intoTop-just a b j (dom-prodˢ d n (≤-pred p))))))

  dom-prod : ∀ {as bs} → Dom as bs → Is-just (prod≾ₑ as bs)
  dom-prod {as} {bs} d with prodˢ≾ₑ (length as + length bs) as bs | dom-prodˢ d _ ≤-refl
  ... | just _ | _ = isJust tt

  altSum-just : ∀ P t {P'} → Is-just (prod≾ₑ P P') → P' ∈ᴬ t → Is-just (altSum≾ₑ P t)
  altSum-just P (alt P')  j inAlt = j
  altSum-just P (P' ∷⁺ t) j inHead with prod≾ₑ P P' | j
  ... | just _ | _ = isJust tt
  altSum-just P (P₀ ∷⁺ t) j (inTail m) with prod≾ₑ P P₀
  ... | just _  = isJust tt
  ... | nothing with altSum≾ₑ P t | altSum-just P t j m
  ...   | just _ | _ = isJust tt

  sum-just : ∀ s t → (∀ {P} → P ∈ᴬ s → Is-just (altSum≾ₑ P t)) → Is-just (sum≾ₑ s t)
  sum-just (alt P)  t f = f inAlt
  sum-just (P ∷⁺ s) t f with altSum≾ₑ P t | f inHead | sum≾ₑ s t | sum-just s t (λ m → f (inTail m))
  ... | just _ | _ | just _ | _ = isJust tt

  decide-justₑ : ∀ ε ε' → Is-just (sum≾ₑ (nrmₑ ε) (foldSumₑ (nrmₑ ε')))
               → Is-just (decide≾ₑ {Q = Q} ε ε')
  decide-justₑ ε ε' j with sum≾ₑ (nrmₑ ε) (foldSumₑ (nrmₑ ε')) | j
  ... | just _ | _ = isJust tt

  -- a product read off its slots, below another so read

  dom-cons[]ₑ : ∀ {c d} → c ≾ₑ d → Dom (consₑ (ac c) []) (consₑ (ac d) [])
  dom-cons[]ₑ {c} {d} p with c ≡ₑ? uₑ | d ≡ₑ? uₑ
  ... | yes _    | yes _    = d[]
  ... | yes refl | no _     = dskipʳ (unit-cₑ p) d[]
  ... | no _     | yes refl = dskipˡ (≾unit-cₑ p) d[]
  ... | no _     | no _     = dmatch (atom-linkₑ (link-cₑ p)) d[]

  dom-consvₑ : ∀ {c d i as bs} → c ≾ₑ d → Dom as bs
             → Dom (consₑ (ac c) (av i ∷ as)) (consₑ (ac d) (av i ∷ bs))
  dom-consvₑ {c} {d} {i} p q with c ≡ₑ? uₑ | d ≡ₑ? uₑ
  ... | yes _    | yes _    = dmatch (atom-linkₑ (link-vₑ i)) q
  ... | yes refl | no _     = dskipʳ (unit-cₑ p) (dmatch (atom-linkₑ (link-vₑ i)) q)
  ... | no _     | yes refl = dskipˡ (≾unit-cₑ p) (dmatch (atom-linkₑ (link-vₑ i)) q)
  ... | no _     | no _     = dmatch (atom-linkₑ (link-cₑ p)) (dmatch (atom-linkₑ (link-vₑ i)) q)

  dom-atomsₑ : ∀ {vs} {s t : Gₑ.Slots {Θ} vs} → s ≤ˢ t → Dom (atomsₑ s) (atomsₑ t)
  dom-atomsₑ (≤⌜⌝ p)   = dom-cons[]ₑ p
  dom-atomsₑ (≤▸ p le) = dom-consvₑ p (dom-atomsₑ le)

  -- the top absorbs any product

  dom-topₑ : ∀ {d} → ⊤ₑ ≾ₑ d → ∀ P → Dom P (consₑ (ac d) [])
  dom-topₑ {d} p P with d ≡ₑ? uₑ
  ... | yes refl = go P
    where
      go : ∀ P → Dom P []
      go []      = d[]
      go (a ∷ P) = dskipˡ (≾unit-topₑ a p) (go P)
  ... | no _ = go P
    where
      go : ∀ P → Dom P (ac d ∷ [])
      go []      = dskipʳ (unit-cₑ (≾ₑ-trans (≾-⊤ₑ uₑ) p)) d[]
      go (a ∷ P) = dtop (ceil-topₑ p) (go P)

------------------------------------------------------------------------
-- A normal product is its slots read back

mutual

  slots-nfₑ : ∀ {Θ} {P : List (EAtom Θ)} → NFₑ P → atomsₑ (proj₂ (slotsₑ nothing P)) ≡ P
  slots-nfₑ (nfᵛ v)    = slots-nfᵛₑ v
  slots-nfₑ (nfc ¬p v) = slots-nfcₑ ¬p v

  slots-nfᵛₑ : ∀ {Θ} {P : List (EAtom Θ)} → NFᵛₑ P → atomsₑ (proj₂ (slotsₑ nothing P)) ≡ P
  slots-nfᵛₑ nf[] with uₑ ≡ₑ? uₑ
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)
  slots-nfᵛₑ (nfv i n) with uₑ ≡ₑ? uₑ
  ... | yes _ = cong (av i ∷_) (slots-nfₑ n)
  ... | no ¬p = ⊥-elim (¬p refl)

  slots-nfcₑ : ∀ {Θ} {c} {P : List (EAtom Θ)} → ¬ (c ≡ uₑ) → NFᵛₑ P
             → atomsₑ (proj₂ (slotsₑ (just c) P)) ≡ ac c ∷ P
  slots-nfcₑ {c = c} ¬p nf[] with c ≡ₑ? uₑ
  ... | yes q = ⊥-elim (¬p q)
  ... | no _  = refl
  slots-nfcₑ {c = c} ¬p (nfv i n) with c ≡ₑ? uₑ
  ... | yes q = ⊥-elim (¬p q)
  ... | no _  = cong (λ l → ac c ∷ av i ∷ l) (slots-nfₑ n)

slots-constₑ : ∀ {Θ} c → slotsₑ {Θ} nothing (consₑ (ac c) []) ≡ ([] , Gₑ.⌜ c ⌝)
slots-constₑ c with c ≡ₑ? uₑ
... | yes refl = refl
... | no _     = refl

------------------------------------------------------------------------
-- An expression is below a join of it and others

join-decideₑ : ∀ {Θ} {Q : Hyps Θ} (x₀ : EExp Θ) xs {x} → x ∈ x₀ ∷ xs
             → Is-just (decide≾ₑ {Q = Q} x (joinₑ x₀ xs))
join-decideₑ {Θ} {Q} x₀ xs {x} w =
  decide-justₑ x Jn (sum-just (nrmₑ x) (foldSumₑ (nrmₑ Jn)) alt-for)
  where
    Jn = joinₑ x₀ xs

    open Searchₑ {Θ} {Q} (tableₑ Q)

    below : ∀ {P Q'} → NFₑ P → (Q' ≡ P) ⊎ TopAltₑ Q' → ∀ {P''} → slotsₑ nothing Q' ≤ᵖ P''
          → Dom {Q = Q} P (atomsₑ (proj₂ P''))
    below n (inj₁ refl) (≤ᵖ-at {t = t} le) =
      subst (λ P₀ → Dom {Q = Q} P₀ (atomsₑ t)) (slots-nfₑ n) (dom-atomsₑ le)
    below {P} n (inj₂ (c , refl , top)) le with subst (_≤ᵖ _) (slots-constₑ {Θ} c) le
    ... | ≤ᵖ-at (≤⌜⌝ p) = dom-topₑ (≾ₑ-trans top p) P

    alt-for : ∀ {P} → P ∈ᴬ nrmₑ x → Is-just (altSum≾ₑ P (foldSumₑ (nrmₑ Jn)))
    alt-for {P} m with nrmₑ-join x₀ xs w m
    ... | Q' , mQ' , k with canonical-≤ (toProdsₑ (nrmₑ Jn)) (∈-map (slotsₑ nothing) mQ')
    ...   | P'' , mP'' , le =
            altSum-just P (foldSumₑ (nrmₑ Jn)) (dom-prod (below (nrmₑ-NF x m) k le))
                        (∈-map (λ P → atomsₑ (proj₂ P)) mP'')

------------------------------------------------------------------------
-- Resource grades

module GEᵣ {Θ : Scope} =
  Groups {RExp Θ} {R} {RVAtom Θ} _≡̂ᵣ_ ≡̂ᵣ-refl ≡̂ᵣ-sym ≡̂ᵣ-trans _·̂ᵣ_ _⊔̂ᵣ_
         ≡̂ᵣ-cong ≡̂ᵣ-cong-⊔ ≡̂ᵣ-idem-⊔ ≡̂ᵣ-comm-⊔ ≡̂ᵣ-assoc-⊔
         ≡̂ᵣ-distribˡ-⊔ ≡̂ᵣ-distribʳ-⊔
         rconst _⊔ᵣ_ ≡̂ᵣ-const-⊔ _≡ᵣ?_ ⟦_⟧ʳᵛ _≟ʳᵛ_ _<ʳᵛ_

module BEᵣ {Θ : Scope} = GEᵣ.Below {Θ} _≾ᵣ_ ≾ᵣ-refl ≾ᵣ-trans ⊔ᵣ-ubˡ ⊔ᵣ-ubʳ

module _ {Θ} {Q : Hyps Θ} where

  open Searchᵣ {Θ} {Q} (tableᵣ Q)

  link-cᵣ : ∀ {c d} → c ≾ᵣ d → Is-just (linkᵣ? {Q = Q} (rc c) (rc d))
  link-cᵣ {c} {d} p with c ≾ᵣ? d
  ... | yes _ = isJust tt
  ... | no ¬p = ⊥-elim (¬p p)

  link-vᵣ : ∀ a → Is-just (linkᵣ? {Q = Q} (varAtomᵣ a) (varAtomᵣ a))
  link-vᵣ (vr i) with i ≟ᶠ i
  ... | yes refl = isJust tt
  ... | no ¬p    = ⊥-elim (¬p refl)
  link-vᵣ (vm i) with i ≟ᶠ i
  ... | yes refl = isJust tt
  ... | no ¬p    = ⊥-elim (¬p refl)

  reach-linkᵣ : ∀ {a b} → Is-just (linkᵣ? {Q = Q} a b) → Is-just (reachᵣ? a b)
  reach-linkᵣ j = <∣>-l j

  atom-linkᵣ : ∀ {a b} → Is-just (linkᵣ? {Q = Q} a b) → Is-just (atom≾ᵣ a b)
  atom-linkᵣ j = <∣>-l j

  ceil-topᵣ : ∀ {ρ d} → ⊤ᵣ ≾ᵣ d → Is-just (ceilᵣ {ρ} (rc d))
  ceil-topᵣ {d = d} p with reachᵣ? (rc ⊤ᵣ) (rc d) | reach-linkᵣ {rc ⊤ᵣ} {rc d} (link-cᵣ p)
  ... | just _  | _  = isJust tt
  ... | nothing | ()

  unit-cᵣ : ∀ {d} → uᵣ ≾ᵣ d → Is-just (unit≾ᵣ (rc d))
  unit-cᵣ {d} p =
    <∣>-r {m₁ = min≾ᵣ (Is-just? uᵣ-least?)} (<∣>-r {m₁ = minᵐ (rc d)} (atom-linkᵣ (link-cᵣ p)))

  ≾unit-cᵣ : ∀ {c} → c ≾ᵣ uᵣ → Is-just (≾unitᵣ (rc c))
  ≾unit-cᵣ p = atom-linkᵣ (link-cᵣ p)

  ≾unit-topᵣ : ∀ a → ⊤ᵣ ≾ᵣ uᵣ → Is-just (≾unitᵣ a)
  ≾unit-topᵣ a p = <∣>-r {m₁ = linkᵣ? a (rc uᵣ)} (<∣>-l (ceil-topᵣ p))

  match-justᵣ : ∀ {ρ ρ'} a b {r : Maybe (Q ⊩ ρ ≾̂ᵣ ρ')} → Is-just (atom≾ᵣ a b) → Is-just r
              → Is-just (matchᵣ a b r)
  match-justᵣ a b {r} ja jr with atom≾ᵣ a b | ja
  ... | just _ | _ with r | jr
  ...   | just _ | _ = isJust tt

  skipʳ-justᵣ : ∀ {ρ ρ'} b {r : Maybe (Q ⊩ ρ ≾̂ᵣ ρ')} → Is-just (unit≾ᵣ b) → Is-just r
              → Is-just (skipʳᵣ b r)
  skipʳ-justᵣ b {r} ja jr with unit≾ᵣ b | ja
  ... | just _ | _ with r | jr
  ...   | just _ | _ = isJust tt

  skipˡ-justᵣ : ∀ {ρ ρ'} a {r : Maybe (Q ⊩ ρ ≾̂ᵣ ρ')} → Is-just (≾unitᵣ a) → Is-just r
              → Is-just (skipˡᵣ a r)
  skipˡ-justᵣ a {r} ja jr with ≾unitᵣ a | ja
  ... | just _ | _ with r | jr
  ...   | just _ | _ = isJust tt

  intoTop-justᵣ : ∀ {ρ ρ'} a b {r : Maybe (Q ⊩ ρ ≾̂ᵣ ⟦ b ⟧ʳᵃ ·̂ᵣ ρ')} → Is-just (absorbs≾ᵣ a b)
                → Is-just r → Is-just (intoTopᵣ a b r)
  intoTop-justᵣ a b {r} ja jr with absorbs≾ᵣ a b | ja
  ... | just _ | _ with r | jr
  ...   | just _ | _ = isJust tt

  data Domᵣ : List (RAtom Θ) → List (RAtom Θ) → Set where
    d[]    : Domᵣ [] []
    dmatch : ∀ {a b as bs} → Is-just (atom≾ᵣ a b) → Domᵣ as bs → Domᵣ (a ∷ as) (b ∷ bs)
    dskipʳ : ∀ {as b bs} → Is-just (unit≾ᵣ b) → Domᵣ as bs → Domᵣ as (b ∷ bs)
    dskipˡ : ∀ {a as bs} → Is-just (≾unitᵣ a) → Domᵣ as bs → Domᵣ (a ∷ as) bs
    dtop   : ∀ {a as b bs} → Is-just (absorbs≾ᵣ a b) → Domᵣ as (b ∷ bs) → Domᵣ (a ∷ as) (b ∷ bs)

  dom-prodˢᵣ : ∀ {as bs} → Domᵣ as bs → ∀ n → length as + length bs ≤ n → Is-just (prodˢ≾ᵣ n as bs)
  dom-prodˢᵣ d[] n p = isJust tt
  dom-prodˢᵣ (dmatch {a} {b} {as} {bs} j d) (suc n) p =
    <∣>-l (match-justᵣ a b j (dom-prodˢᵣ d n (step≤ {length as} p)))
  dom-prodˢᵣ (dskipʳ {[]} {b} {bs} j d) (suc n) p =
    <∣>-l (skipʳ-justᵣ b j (dom-prodˢᵣ d n (≤-pred p)))
  dom-prodˢᵣ (dskipʳ {a ∷ as} {b} {bs} j d) (suc n) p =
    <∣>-r {m₁ = matchᵣ a b (prodˢ≾ᵣ n as bs)}
      (<∣>-l (skipʳ-justᵣ b j (dom-prodˢᵣ d n (stepʳ≤ {length (a ∷ as)} p))))
  dom-prodˢᵣ (dskipˡ {a} {as} {[]} j d) (suc n) p =
    <∣>-l (skipˡ-justᵣ a j (dom-prodˢᵣ d n (≤-pred p)))
  dom-prodˢᵣ (dskipˡ {a} {as} {b ∷ bs} j d) (suc n) p =
    <∣>-r {m₁ = matchᵣ a b (prodˢ≾ᵣ n as bs)}
      (<∣>-r {m₁ = skipʳᵣ b (prodˢ≾ᵣ n (a ∷ as) bs)}
        (<∣>-l (skipˡ-justᵣ a j (dom-prodˢᵣ d n (≤-pred p)))))
  dom-prodˢᵣ (dtop {a} {as} {b} {bs} j d) (suc n) p =
    <∣>-r {m₁ = matchᵣ a b (prodˢ≾ᵣ n as bs)}
      (<∣>-r {m₁ = skipʳᵣ b (prodˢ≾ᵣ n (a ∷ as) bs)}
        (<∣>-r {m₁ = skipˡᵣ a (prodˢ≾ᵣ n as (b ∷ bs))}
          (<∣>-l (intoTop-justᵣ a b j (dom-prodˢᵣ d n (≤-pred p))))))

  dom-prodᵣ : ∀ {as bs} → Domᵣ as bs → Is-just (prod≾ᵣ as bs)
  dom-prodᵣ {as} {bs} d with prodˢ≾ᵣ (length as + length bs) as bs | dom-prodˢᵣ d _ ≤-refl
  ... | just _ | _ = isJust tt

  altSum-justᵣ : ∀ P t {P'} → Is-just (prod≾ᵣ P P') → P' ∈ᴬ t → Is-just (altSum≾ᵣ P t)
  altSum-justᵣ P (alt P')  j inAlt = j
  altSum-justᵣ P (P' ∷⁺ t) j inHead with prod≾ᵣ P P' | j
  ... | just _ | _ = isJust tt
  altSum-justᵣ P (P₀ ∷⁺ t) j (inTail m) with prod≾ᵣ P P₀
  ... | just _  = isJust tt
  ... | nothing with altSum≾ᵣ P t | altSum-justᵣ P t j m
  ...   | just _ | _ = isJust tt

  sum-justᵣ : ∀ s t → (∀ {P} → P ∈ᴬ s → Is-just (altSum≾ᵣ P t)) → Is-just (sum≾ᵣ s t)
  sum-justᵣ (alt P)  t f = f inAlt
  sum-justᵣ (P ∷⁺ s) t f with altSum≾ᵣ P t | f inHead | sum≾ᵣ s t | sum-justᵣ s t (λ m → f (inTail m))
  ... | just _ | _ | just _ | _ = isJust tt

  decide-justᵣ : ∀ ρ ρ' → Is-just (sum≾ᵣ (nrmᵣ ρ) (foldSumᵣ (nrmᵣ ρ')))
               → Is-just (decide≾ᵣ {Q = Q} ρ ρ')
  decide-justᵣ ρ ρ' j with sum≾ᵣ (nrmᵣ ρ) (foldSumᵣ (nrmᵣ ρ')) | j
  ... | just _ | _ = isJust tt

  dom-cons[]ᵣ : ∀ {c d} → c ≾ᵣ d → Domᵣ (consᵣ (rc c) []) (consᵣ (rc d) [])
  dom-cons[]ᵣ {c} {d} p with c ≡ᵣ? uᵣ | d ≡ᵣ? uᵣ
  ... | yes _    | yes _    = d[]
  ... | yes refl | no _     = dskipʳ (unit-cᵣ p) d[]
  ... | no _     | yes refl = dskipˡ (≾unit-cᵣ p) d[]
  ... | no _     | no _     = dmatch (atom-linkᵣ (link-cᵣ p)) d[]

  dom-consvᵣ : ∀ {c d} a {as bs} → c ≾ᵣ d → Domᵣ as bs
             → Domᵣ (consᵣ (rc c) (varAtomᵣ a ∷ as)) (consᵣ (rc d) (varAtomᵣ a ∷ bs))
  dom-consvᵣ {c} {d} (vr i) p q with c ≡ᵣ? uᵣ | d ≡ᵣ? uᵣ
  ... | yes _    | yes _    = dmatch (atom-linkᵣ (link-vᵣ (vr i))) q
  ... | yes refl | no _     = dskipʳ (unit-cᵣ p) (dmatch (atom-linkᵣ (link-vᵣ (vr i))) q)
  ... | no _     | yes refl = dskipˡ (≾unit-cᵣ p) (dmatch (atom-linkᵣ (link-vᵣ (vr i))) q)
  ... | no _     | no _     =
        dmatch (atom-linkᵣ (link-cᵣ p)) (dmatch (atom-linkᵣ (link-vᵣ (vr i))) q)
  dom-consvᵣ {c} {d} (vm i) p q with c ≡ᵣ? uᵣ | d ≡ᵣ? uᵣ
  ... | yes _    | yes _    = dmatch (atom-linkᵣ (link-vᵣ (vm i))) q
  ... | yes refl | no _     = dskipʳ (unit-cᵣ p) (dmatch (atom-linkᵣ (link-vᵣ (vm i))) q)
  ... | no _     | yes refl = dskipˡ (≾unit-cᵣ p) (dmatch (atom-linkᵣ (link-vᵣ (vm i))) q)
  ... | no _     | no _     =
        dmatch (atom-linkᵣ (link-cᵣ p)) (dmatch (atom-linkᵣ (link-vᵣ (vm i))) q)

  dom-atomsᵣ : ∀ {vs} {s t : Gᵣ.Slots {Θ} vs} → BEᵣ._≤ˢ_ s t → Domᵣ (atomsᵣ s) (atomsᵣ t)
  dom-atomsᵣ (BEᵣ.≤⌜⌝ p)             = dom-cons[]ᵣ p
  dom-atomsᵣ (BEᵣ.≤▸ {a = a} p le)   = dom-consvᵣ a p (dom-atomsᵣ le)

  dom-topᵣ : ∀ {d} → ⊤ᵣ ≾ᵣ d → ∀ P → Domᵣ P (consᵣ (rc d) [])
  dom-topᵣ {d} p P with d ≡ᵣ? uᵣ
  ... | yes refl = go P
    where
      go : ∀ P → Domᵣ P []
      go []      = d[]
      go (a ∷ P) = dskipˡ (≾unit-topᵣ a p) (go P)
  ... | no _ = go P
    where
      go : ∀ P → Domᵣ P (rc d ∷ [])
      go []      = dskipʳ (unit-cᵣ (≾ᵣ-trans (≾-⊤ᵣ uᵣ) p)) d[]
      go (a ∷ P) = dtop (ceil-topᵣ p) (go P)

mutual

  slots-nfᵣ : ∀ {Θ} {P : List (RAtom Θ)} → NFᵣ P → atomsᵣ (proj₂ (slotsᵣ nothing P)) ≡ P
  slots-nfᵣ (nfᵛ v)    = slots-nfᵛᵣ v
  slots-nfᵣ (nfc ¬p v) = slots-nfcᵣ ¬p v

  slots-nfᵛᵣ : ∀ {Θ} {P : List (RAtom Θ)} → NFᵛᵣ P → atomsᵣ (proj₂ (slotsᵣ nothing P)) ≡ P
  slots-nfᵛᵣ nf[] with uᵣ ≡ᵣ? uᵣ
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)
  slots-nfᵛᵣ (nfv i n) with uᵣ ≡ᵣ? uᵣ
  ... | yes _ = cong (rv i ∷_) (slots-nfᵣ n)
  ... | no ¬p = ⊥-elim (¬p refl)
  slots-nfᵛᵣ (nfm i n) with uᵣ ≡ᵣ? uᵣ
  ... | yes _ = cong (rm i ∷_) (slots-nfᵣ n)
  ... | no ¬p = ⊥-elim (¬p refl)

  slots-nfcᵣ : ∀ {Θ} {c} {P : List (RAtom Θ)} → ¬ (c ≡ uᵣ) → NFᵛᵣ P
             → atomsᵣ (proj₂ (slotsᵣ (just c) P)) ≡ rc c ∷ P
  slots-nfcᵣ {c = c} ¬p nf[] with c ≡ᵣ? uᵣ
  ... | yes q = ⊥-elim (¬p q)
  ... | no _  = refl
  slots-nfcᵣ {c = c} ¬p (nfv i n) with c ≡ᵣ? uᵣ
  ... | yes q = ⊥-elim (¬p q)
  ... | no _  = cong (λ l → rc c ∷ rv i ∷ l) (slots-nfᵣ n)
  slots-nfcᵣ {c = c} ¬p (nfm i n) with c ≡ᵣ? uᵣ
  ... | yes q = ⊥-elim (¬p q)
  ... | no _  = cong (λ l → rc c ∷ rm i ∷ l) (slots-nfᵣ n)

slots-constᵣ : ∀ {Θ} c → slotsᵣ {Θ} nothing (consᵣ (rc c) []) ≡ ([] , Gᵣ.⌜ c ⌝)
slots-constᵣ c with c ≡ᵣ? uᵣ
... | yes refl = refl
... | no _     = refl

join-decideᵣ : ∀ {Θ} {Q : Hyps Θ} (x₀ : RExp Θ) xs {x} → x ∈ x₀ ∷ xs
             → Is-just (decide≾ᵣ {Q = Q} x (joinᵣ x₀ xs))
join-decideᵣ {Θ} {Q} x₀ xs {x} w =
  decide-justᵣ x Jn (sum-justᵣ (nrmᵣ x) (foldSumᵣ (nrmᵣ Jn)) alt-for)
  where
    Jn = joinᵣ x₀ xs

    open Searchᵣ {Θ} {Q} (tableᵣ Q)

    below : ∀ {P Q'} → NFᵣ P → (Q' ≡ P) ⊎ TopAltᵣ Q' → ∀ {P''} → BEᵣ._≤ᵖ_ (slotsᵣ nothing Q') P''
          → Domᵣ {Q = Q} P (atomsᵣ (proj₂ P''))
    below n (inj₁ refl) (BEᵣ.≤ᵖ-at {t = t} le) =
      subst (λ P₀ → Domᵣ {Q = Q} P₀ (atomsᵣ t)) (slots-nfᵣ n) (dom-atomsᵣ le)
    below {P} n (inj₂ (c , refl , top)) le with subst (λ z → BEᵣ._≤ᵖ_ z _) (slots-constᵣ {Θ} c) le
    ... | BEᵣ.≤ᵖ-at (BEᵣ.≤⌜⌝ p) = dom-topᵣ (≾ᵣ-trans top p) P

    alt-for : ∀ {P} → P ∈ᴬ nrmᵣ x → Is-just (altSum≾ᵣ P (foldSumᵣ (nrmᵣ Jn)))
    alt-for {P} m with nrmᵣ-join x₀ xs w m
    ... | Q' , mQ' , k with BEᵣ.canonical-≤ (toProdsᵣ (nrmᵣ Jn)) (∈-map (slotsᵣ nothing) mQ')
    ...   | P'' , mP'' , le =
            altSum-justᵣ P (foldSumᵣ (nrmᵣ Jn)) (dom-prodᵣ (below (nrmᵣ-NF x m) k le))
                         (∈-map (λ P → atomsᵣ (proj₂ P)) mP'')
