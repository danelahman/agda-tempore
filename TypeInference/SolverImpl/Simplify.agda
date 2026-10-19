------------------------------------------------------------------
-- Normalising, settling and pruning a reported hypothesis set  --
--                                                              --
-- `simplify` proceeds in four steps.                           --
--   * It writes the set in canonical form (`canonᴴ`): every    --
--     grade expression canonical, and an ordering with a join  --
--     on its left side split into one ordering per             --
--     alternative.                                             --
--   * It settles every `disj` entry one of whose sides is      --
--     settled: a met eternality demand or an entailed grade    --
--     ordering drops the entry, a refuted eternality demand    --
--     leaves the grade ordering, and a refuted grade leaves    --
--     the eternality atoms, in skeleton order.                 --
--   * It drops each disjunction entailed by the others, namely --
--     one with the type of another whose grade is entailed     --
--     above its own; of two that entail each other, the later  --
--     is kept (`walkᵈ`).                                       --
--   * It prunes: a subtyping or eternality atom entailed by    --
--     the atoms kept before it is dropped, entailment there    --
--     being reachability in a finite digraph, and a grade      --
--     ordering is dropped when its two sides coincide or it    --
--     repeats one kept before it; the atoms kept stay in       --
--     place. The grade orderings are finally listed by the     --
--     skeletons of their two sides.                            --
--                                                              --
-- `trim` settles the disjunctions again and drops those        --
-- entailed by the others, drops every subtyping atom entailed  --
-- by those kept and those not yet examined, the atom itself    --
-- left out, prunes the eternality atoms along the subtyping    --
-- atoms left, then drops every grade ordering entailed by      --
-- those kept and those not yet examined, and every ordering    --
-- that holds outright.                                         --
--                                                              --
-- For settling, for the disjunctions and for `trim`, an        --
-- ordering is decided at the strength `full` of `Entail` from  --
-- the orderings of the set read, and refuted against the unit  --
-- by `refute≾u`; two types are compared up to the sameness of --
-- their grades (`sameᵛ?`).                                     --
--                                                              --
-- Contract. `simplify Q` and `trim Q` entail `Q`               --
-- (`simplify-⊩`, `trim-⊩`), and every closed instance of `Q`   --
-- is one of each (`simplify-⊨`, `trim-⊨`); settling a          --
-- disjunction by a refutation holds only at the instances.     --
-- That the result is irredundant is not claimed: an atom is    --
-- dropped only where a test proves it entailed. The            --
-- simplification applies to the report only; the solver and    --
-- `solve-principal` are unaffected.                            --
------------------------------------------------------------------

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)

open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Simplify
  (S : LanguageSpec)
  where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Hyps      S
open import TypeInference.OpenSyntax.Instances S
  using (_⊨ᴴ_; ⊨ᴴ-trans; ⊩ᴴ-⊨ᴴ; VarOK-∅; val-≾ᵣ⁻)

open import Syntax.BaseTypes using (module BaseTypes)
open BaseTypes BTs using (_≡ᵇ?_)

open import TypeInference.SolverImpl.Core.Rigid S using (zip₂-just)

open import TypeInference.SolverImpl.Canon  S using (canonᴴ; canonᴴ-⊩; canonᴴ-⊩⁻)
open import TypeInference.SolverImpl.Eliminate S using (Elim; mkElim)
open import TypeInference.SolverImpl.Product S using (_≺ᵣ_; _≺ₑ_)
open import TypeInference.SolverImpl.Resid  S using (etDec; etDec-sound; etDec-compl; etDec-refute)
open import TypeInference.SolverImpl.Entail S
  using (decideᵣ; decideₑ; full; memʳ?; memᵉ?; memʳ-⊩; memᵉ-⊩; refute≾u)

-- Derivations reading only a list of subtyping hypotheses and a list
-- of eternality atoms: `_⊢ᵖ_≾_` mirrors `_⊩ᵗᵛ_≾_`, `Etᴾ` mirrors
-- `_⊩ᴱ_` at a type variable. Eternality moves along a hypothesis in
-- both directions, subtyping only forwards.

infix 4 _⊢ᵖ_≾_

data _⊢ᵖ_≾_ {n : ℕ} (l : List (Fin n × Fin n)) : Fin n → Fin n → Set where
  stopᵖ : ∀ {α} → l ⊢ᵖ α ≾ α
  stepᵖ : ∀ {α β γ} → (α , β) ∈ l → l ⊢ᵖ β ≾ γ → l ⊢ᵖ α ≾ γ

data Etᴾ {n : ℕ} (l : List (Fin n × Fin n)) (as : List (Fin n)) : Fin n → Set where
  atomᴾ : ∀ {α} → α ∈ as → Etᴾ l as α
  downᴾ : ∀ {α β} → (α , β) ∈ l → Etᴾ l as β → Etᴾ l as α
  upᴾ   : ∀ {α β} → (α , β) ∈ l → Etᴾ l as α → Etᴾ l as β

transᵖ : ∀ {n} {l : List (Fin n × Fin n)} {α β γ}
       → l ⊢ᵖ α ≾ β → l ⊢ᵖ β ≾ γ → l ⊢ᵖ α ≾ γ
transᵖ stopᵖ       q = q
transᵖ (stepᵖ m p) q = stepᵖ m (transᵖ p q)

⊢ᵖ-mono : ∀ {n} {l l' : List (Fin n × Fin n)} {α β}
        → (∀ {p} → p ∈ l → p ∈ l') → l ⊢ᵖ α ≾ β → l' ⊢ᵖ α ≾ β
⊢ᵖ-mono k stopᵖ       = stopᵖ
⊢ᵖ-mono k (stepᵖ m p) = stepᵖ (k m) (⊢ᵖ-mono k p)

⊢ᵖ-⊩ : ∀ {Θ} {Q : Hyps Θ} {l α β} → (∀ {p} → p ∈ l → p ∈ subᵥ Q)
     → l ⊢ᵖ α ≾ β → Q ⊩ᵗᵛ α ≾ β
⊢ᵖ-⊩ k stopᵖ       = reflᵗᵛ
⊢ᵖ-⊩ k (stepᵖ m p) = transᵗᵛ (hypᵗᵛ (k m)) (⊢ᵖ-⊩ k p)

⊢ᵖ-⊩' : ∀ {Θ} {Q : Hyps Θ} {l α β} → (∀ {p} → p ∈ l → Q ⊩ᵗᵛ proj₁ p ≾ proj₂ p)
      → l ⊢ᵖ α ≾ β → Q ⊩ᵗᵛ α ≾ β
⊢ᵖ-⊩' k stopᵖ       = reflᵗᵛ
⊢ᵖ-⊩' k (stepᵖ m p) = transᵗᵛ (k m) (⊢ᵖ-⊩' k p)

Etᴾ-mono : ∀ {n} {l l' : List (Fin n × Fin n)} {as as' : List (Fin n)} {α}
         → (∀ {p} → p ∈ l → p ∈ l') → (∀ {β} → β ∈ as → β ∈ as')
         → Etᴾ l as α → Etᴾ l' as' α
Etᴾ-mono k j (atomᴾ m)    = atomᴾ (j m)
Etᴾ-mono k j (downᴾ m et) = downᴾ (k m) (Etᴾ-mono k j et)
Etᴾ-mono k j (upᴾ m et)   = upᴾ (k m) (Etᴾ-mono k j et)

Etᴾ-⊩' : ∀ {Θ} {Q : Hyps Θ} {l as α} → (∀ {p} → p ∈ l → p ∈ subᵥ Q)
       → (∀ {β} → β ∈ as → Q ⊩ᴱ tvar β) → Etᴾ l as α → Q ⊩ᴱ tvar α
Etᴾ-⊩' k j (atomᴾ m)    = j m
Etᴾ-⊩' k j (downᴾ m et) = et-subˡ (hypᵗᵛ (k m)) (Etᴾ-⊩' k j et)
Etᴾ-⊩' k j (upᴾ m et)   = et-subʳ (hypᵗᵛ (k m)) (Etᴾ-⊩' k j et)

Etᴾ-⊩ : ∀ {Θ} {Q : Hyps Θ} {l as α} → (∀ {p} → p ∈ l → p ∈ subᵥ Q)
      → (∀ {β} → β ∈ as → β ∈ ets Q) → Etᴾ l as α → Q ⊩ᴱ tvar α
Etᴾ-⊩ k j = Etᴾ-⊩' k (λ m → et-hyp (j m))

-- Both searches saturate a labelled vertex set along the hypotheses,
-- one round per edge: a shortest path uses at most that many.

module _ {n : ℕ} (l : List (Fin n × Fin n)) where

  findᴱ : ∀ {as} → List (Σ[ α ∈ Fin n ] Etᴾ l as α) → (α : Fin n)
        → Maybe (Etᴾ l as α)
  findᴱ []            α = nothing
  findᴱ ((β , w) ∷ s) α with α ≟ᶠ β
  ... | yes refl = just w
  ... | no  _    = findᴱ s α

  growᴱ : ∀ {as} → (m : List (Fin n × Fin n)) → (∀ {p} → p ∈ m → p ∈ l)
        → List (Σ[ α ∈ Fin n ] Etᴾ l as α) → List (Σ[ α ∈ Fin n ] Etᴾ l as α)
  growᴱ []            k s = s
  growᴱ ((α , β) ∷ m) k s with growᴱ m (λ q → k (there q)) s
  ... | s' with findᴱ s' α | findᴱ s' β
  ...   | just w  | nothing = (β , upᴾ (k (here refl)) w) ∷ s'
  ...   | nothing | just w  = (α , downᴾ (k (here refl)) w) ∷ s'
  ...   | _       | _       = s'

  satᴱ : ∀ {as} → ℕ → List (Σ[ α ∈ Fin n ] Etᴾ l as α)
       → List (Σ[ α ∈ Fin n ] Etᴾ l as α)
  satᴱ ℕ.zero    s = s
  satᴱ (ℕ.suc n) s = satᴱ n (growᴱ l (λ q → q) s)

  seedᴱ : ∀ {as} → (bs : List (Fin n)) → (∀ {β} → β ∈ bs → β ∈ as)
        → List (Σ[ α ∈ Fin n ] Etᴾ l as α)
  seedᴱ []       k = []
  seedᴱ (β ∷ bs) k = (β , atomᴾ (k (here refl))) ∷ seedᴱ bs (λ q → k (there q))

  etᴾ? : (as : List (Fin n)) → (α : Fin n) → Maybe (Etᴾ l as α)
  etᴾ? as = findᴱ (satᴱ (length l) (seedᴱ as (λ q → q)))

  findᵖ : ∀ {α} → List (Σ[ γ ∈ Fin n ] (l ⊢ᵖ α ≾ γ)) → (β : Fin n)
        → Maybe (l ⊢ᵖ α ≾ β)
  findᵖ []            β = nothing
  findᵖ ((γ , w) ∷ s) β with β ≟ᶠ γ
  ... | yes refl = just w
  ... | no  _    = findᵖ s β

  growᵖ : ∀ {α} → (m : List (Fin n × Fin n)) → (∀ {p} → p ∈ m → p ∈ l)
        → List (Σ[ γ ∈ Fin n ] (l ⊢ᵖ α ≾ γ))
        → List (Σ[ γ ∈ Fin n ] (l ⊢ᵖ α ≾ γ))
  growᵖ []            k s = s
  growᵖ ((β , γ) ∷ m) k s with growᵖ m (λ q → k (there q)) s
  ... | s' with findᵖ s' β | findᵖ s' γ
  ...   | just w | nothing = (γ , transᵖ w (stepᵖ (k (here refl)) stopᵖ)) ∷ s'
  ...   | _      | _       = s'

  satᵖ : ∀ {α} → ℕ → List (Σ[ γ ∈ Fin n ] (l ⊢ᵖ α ≾ γ))
       → List (Σ[ γ ∈ Fin n ] (l ⊢ᵖ α ≾ γ))
  satᵖ ℕ.zero    s = s
  satᵖ (ℕ.suc n) s = satᵖ n (growᵖ l (λ q → q) s)

  reach? : (α β : Fin n) → Maybe (l ⊢ᵖ α ≾ β)
  reach? α = findᵖ (satᵖ (length l) ((α , stopᵖ) ∷ []))

-- Eternality of every atom a type decomposes to, from the set itself

ets? : ∀ {Θ} → (Q : Hyps Θ) → (as : List (TyVar Θ))
     → Maybe (∀ {α} → α ∈ as → Q ⊩ᴱ tvar α)
ets? Q []       = just (λ ())
ets? Q (α ∷ as) with etᴾ? (subᵥ Q) (ets Q) α | ets? Q as
... | just w | just k = just (λ { (here refl) → Etᴾ-⊩ (λ q → q) (λ q → q) w
                                ; (there m)   → k m })
... | _      | _      = nothing

-- Insertion into a list ordered by `_≺_`, after every entry below the
-- one inserted, and the sort built from it, which only permutes the
-- list

module _ {A : Set} (_≺_ : A → A → 𝔹) where

  insertᴼ : A → List A → List A
  insertᴼ p []      = p ∷ []
  insertᴼ p (q ∷ l) with q ≺ p
  ... | true  = q ∷ insertᴼ p l
  ... | false = p ∷ q ∷ l

  sortᴼ : List A → List A
  sortᴼ []      = []
  sortᴼ (p ∷ l) = insertᴼ p (sortᴼ l)

  insertᴼ-⊆ : ∀ p l {x} → x ∈ insertᴼ p l → x ∈ p ∷ l
  insertᴼ-⊆ p []      m = m
  insertᴼ-⊆ p (q ∷ l) m with q ≺ p
  insertᴼ-⊆ p (q ∷ l) (here refl) | true = there (here refl)
  insertᴼ-⊆ p (q ∷ l) (there m)   | true with insertᴼ-⊆ p l m
  ... | here refl = here refl
  ... | there m'  = there (there m')
  insertᴼ-⊆ p (q ∷ l) m           | false = m

  insertᴼ-⊇ : ∀ p l {x} → x ∈ p ∷ l → x ∈ insertᴼ p l
  insertᴼ-⊇ p []      m = m
  insertᴼ-⊇ p (q ∷ l) m with q ≺ p
  insertᴼ-⊇ p (q ∷ l) (here refl)         | true  = there (insertᴼ-⊇ p l (here refl))
  insertᴼ-⊇ p (q ∷ l) (there (here refl)) | true  = here refl
  insertᴼ-⊇ p (q ∷ l) (there (there m))   | true  = there (insertᴼ-⊇ p l (there m))
  insertᴼ-⊇ p (q ∷ l) m                   | false = m

  sortᴼ-⊆ : ∀ l {x} → x ∈ sortᴼ l → x ∈ l
  sortᴼ-⊆ (p ∷ l) m with insertᴼ-⊆ p (sortᴼ l) m
  ... | here refl = here refl
  ... | there m'  = there (sortᴼ-⊆ l m')

  sortᴼ-⊇ : ∀ l {x} → x ∈ l → x ∈ sortᴼ l
  sortᴼ-⊇ (p ∷ l) (here refl) = insertᴼ-⊇ p (sortᴼ l) (here refl)
  sortᴼ-⊇ (p ∷ l) (there m)   = insertᴼ-⊇ p (sortᴼ l) (there (sortᴼ-⊇ l m))

-- A walk down a list dropping every entry a test settles, those kept
-- staying in place. The test sees the entries kept so far and those
-- not yet examined.

module Walk {A : Set} (Ok : List A → List A → A → Set)
            (test : (seen rest : List A) → (p : A) → Maybe (Ok seen rest p))
            where

  walk : List A → List A → List A
  walk seen []      = []
  walk seen (p ∷ l) with test seen l p
  ... | just _  = walk seen l
  ... | nothing = p ∷ walk (p ∷ seen) l

  walk-⊆ : (seen l : List A) → ∀ {p} → p ∈ walk seen l → p ∈ l
  walk-⊆ seen (p₀ ∷ l) m with test seen l p₀
  walk-⊆ seen (p₀ ∷ l) m           | just _  = there (walk-⊆ seen l m)
  walk-⊆ seen (p₀ ∷ l) (here refl) | nothing = here refl
  walk-⊆ seen (p₀ ∷ l) (there m)   | nothing = there (walk-⊆ (p₀ ∷ seen) l m)

  -- A property that a settled entry has whenever everything its test
  -- saw has it, and that holds of the entries seen and those kept,
  -- holds of every entry

  walk-⊨ : (P : A → Set)
         → (∀ seen rest {p} → Ok seen rest p → (∀ {q} → q ∈ seen ++ rest → P q) → P p)
         → (seen l : List A) → (∀ {q} → q ∈ seen → P q)
         → (∀ {q} → q ∈ walk seen l → P q)
         → ∀ {q} → q ∈ l → P q
  walk-⊨ P close seen (p₀ ∷ l) hs hk m with test seen l p₀
  walk-⊨ P close seen (p₀ ∷ l) hs hk (here refl) | just d  =
    close seen l d (λ q → [ hs , walk-⊨ P close seen l hs hk ]′ (∈-++⁻ seen q))
  walk-⊨ P close seen (p₀ ∷ l) hs hk (there m)   | just _  =
    walk-⊨ P close seen l hs hk m
  walk-⊨ P close seen (p₀ ∷ l) hs hk (here refl) | nothing = hk (here refl)
  walk-⊨ P close seen (p₀ ∷ l) hs hk (there m)   | nothing =
    walk-⊨ P close (p₀ ∷ seen) l
           (λ { (here refl) → hk (here refl) ; (there q) → hs q })
           (λ q → hk (there q)) m

-- One disjunction, settled at the strength `full`, by the set
-- itself and by refutation against the unit

settle : ∀ {Θ} → OVType Θ → RExp Θ → Hyps Θ → Hyps Θ
settle A ρ Q with decideᵣ full Q ρ ûᵣ
... | just _  = Q
... | nothing with etDec A
...   | nothing = hyps (ets Q) (subᵥ Q) (ordᵣ Q ++ (ρ , ûᵣ) ∷ []) (ordₑ Q) (disj Q)
...   | just αs with ets? Q αs
...     | just _  = Q
...     | nothing with refute≾u ρ
...       | just _  = hyps (αs ++ ets Q) (subᵥ Q) (ordᵣ Q) (ordₑ Q) (disj Q)
...       | nothing = hyps (ets Q) (subᵥ Q) (ordᵣ Q) (ordₑ Q) ((A , ρ) ∷ disj Q)

-- A settled disjunction is entailed by the set it leaves, which entails
-- the set it came from

settle-⊩ : ∀ {Θ} → (A : OVType Θ) → (ρ : RExp Θ) → (Q : Hyps Θ)
         → (settle A ρ Q ⊩ᴴ Q) × VarOK (settle A ρ Q) A ρ
settle-⊩ A ρ Q with decideᵣ full Q ρ ûᵣ
... | just d  = ⊩ᴴ-refl , ≾ᵘ-ok d
... | nothing with etDec A in e
...   | nothing =
        ⊆ᴴ-⊩ (mk⊆ᴴ (λ m → m) (λ m → m) ∈-++⁺ˡ (λ m → m) (λ m → m))
        , ≾ᵘ-ok (hypᵣ (∈-++⁺ʳ (ordᵣ Q) (here refl)))
...   | just αs with ets? Q αs
...     | just k  = ⊩ᴴ-refl , et-ok (etDec-sound A e k)
...     | nothing with refute≾u ρ
...       | just _  =
            ⊆ᴴ-⊩ (mk⊆ᴴ (∈-++⁺ʳ αs) (λ m → m) (λ m → m) (λ m → m) (λ m → m))
            , et-ok (etDec-sound A e (λ m → et-hyp (∈-++⁺ˡ m)))
...       | nothing =
            ⊆ᴴ-⊩ (mk⊆ᴴ (λ m → m) (λ m → m) (λ m → m) (λ m → m) there)
            , hyp-ok₀ (here refl)

-- At an instance meeting the disjunction, an instance of the set is one
-- of the set it leaves: a type `etDec` refutes is eternal at no
-- instance, and a refuted grade is below the unit at none.

settle-inst : ∀ {Θ} → (A : OVType Θ) → (ρ : RExp Θ) → (Q : Hyps Θ) → (δ : Subst Θ ∅ˢ)
            → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ) → ∅ᴴ ⊩ᴴ Q [ δ ] → ∅ᴴ ⊩ᴴ settle A ρ Q [ δ ]
settle-inst A ρ Q δ d h with decideᵣ full Q ρ ûᵣ
... | just _  = h
... | nothing with etDec A in e
...   | nothing = mk⊩ᴴ (⊩ets h) (⊩subᵥ h) ordR (⊩ordₑ h) (⊩disj h)
      where
        ordR : ∀ {ρ₀ ρ₀'} → (ρ₀ , ρ₀') ∈ ordᵣ Q ++ (ρ , ûᵣ) ∷ []
             → ∅ᴴ ⊩ ρ₀ [ δ ]ʳ ≾̂ᵣ ρ₀' [ δ ]ʳ
        ordR m with ∈-++⁻ (ordᵣ Q) m
        ... | inj₂ (here refl) = [ (λ et → ⊥-elim (etDec-refute A e δ et)) , val-≾ᵣ⁻ ]′ (VarOK-∅ d)
        ... | inj₁ m'          = ⊩ordᵣ h m'
...   | just αs with ets? Q αs
...     | just _  = h
...     | nothing with refute≾u ρ
...       | just ref = mk⊩ᴴ et' (⊩subᵥ h) (⊩ordᵣ h) (⊩ordₑ h) (⊩disj h)
      where
        etA : ∅ᴴ ⊩ᴱ A [ δ ]ᵛ
        etA = [ (λ et → et) , (λ le → ⊥-elim (ref δ le)) ]′ (VarOK-∅ d)

        et' : ∀ {β} → β ∈ (αs ++ ets Q) → ∅ᴴ ⊩ᴱ sTy δ β
        et' m = [ etDec-compl A e δ etA , ⊩ets h ]′ (∈-++⁻ αs m)
...       | nothing = mk⊩ᴴ (⊩ets h) (⊩subᵥ h) (⊩ordᵣ h) (⊩ordₑ h) dsj'
      where
        dsj' : ∀ {A₀ ρ₀} → (A₀ , ρ₀) ∈ ((A , ρ) ∷ disj Q)
             → VarOK ∅ᴴ (A₀ [ δ ]ᵛ) (ρ₀ [ δ ]ʳ)
        dsj' (here refl) = d
        dsj' (there m)   = ⊩disj h m

settleAll : ∀ {Θ} → List (OVType Θ × RExp Θ) → Hyps Θ → Hyps Θ
settleAll []             Q₀ = Q₀
settleAll ((A , ρ) ∷ l) Q₀ = settle A ρ (settleAll l Q₀)

settleAll-⊩ : ∀ {Θ} → (l : List (OVType Θ × RExp Θ)) → (Q₀ : Hyps Θ)
            → (settleAll l Q₀ ⊩ᴴ Q₀) × (∀ {A ρ} → (A , ρ) ∈ l → VarOK (settleAll l Q₀) A ρ)
settleAll-⊩ []             Q₀ = ⊩ᴴ-refl , λ ()
settleAll-⊩ ((A , ρ) ∷ l) Q₀ with settle-⊩ A ρ (settleAll l Q₀) | settleAll-⊩ l Q₀
... | h , d | h' , k = ⊩ᴴ-trans h h' , λ { (here refl) → d ; (there m) → ⊩ᴴ-VarOK h (k m) }

settleAll-inst : ∀ {Θ} → (l : List (OVType Θ × RExp Θ)) → (Q₀ : Hyps Θ)
               → (δ : Subst Θ ∅ˢ)
               → (∀ {A ρ} → (A , ρ) ∈ l → VarOK ∅ᴴ (A [ δ ]ᵛ) (ρ [ δ ]ʳ))
               → ∅ᴴ ⊩ᴴ Q₀ [ δ ] → ∅ᴴ ⊩ᴴ settleAll l Q₀ [ δ ]
settleAll-inst []             Q₀ δ k h = h
settleAll-inst ((A , ρ) ∷ l) Q₀ δ k h =
  settle-inst A ρ (settleAll l Q₀) δ (k (here refl))
              (settleAll-inst l Q₀ δ (λ m → k (there m)) h)

-- The set with its disjunctions taken out, to be settled one at a time

split : ∀ {Θ} → Hyps Θ → Hyps Θ
split Q₀ = hyps (ets Q₀) (subᵥ Q₀) (ordᵣ Q₀) (ordₑ Q₀) []

-- Types the same up to the sameness of their grades, which makes them
-- convertible

sameᵛ? : ∀ {Θ} → (A A' : OVType Θ) → Maybe (A ≡̂ᵛ A')
sameᶜ? : ∀ {Θ} → (C C' : OCType Θ) → Maybe (C ≡̂ᶜ C')

sameᵛ? (tvar α) (tvar β) with α ≟ᶠ β
... | yes refl = just tvar≡̂
... | no _     = nothing
sameᵛ? (Base b) (Base b') with b ≡ᵇ? b'
... | yes refl = just Base≡̂
... | no _     = nothing
sameᵛ? Unit Unit = just Unit≡̂
sameᵛ? Bool Bool = just Bool≡̂
sameᵛ? Nat Nat = just Nat≡̂
sameᵛ? (A |×| B) (A' |×| B') with sameᵛ? A A' | sameᵛ? B B'
... | just p | just q = just (p |×|≡̂ q)
... | _      | _      = nothing
sameᵛ? (A |+| B) (A' |+| B') with sameᵛ? A A' | sameᵛ? B B'
... | just p | just q = just (p |+|≡̂ q)
... | _      | _      = nothing
sameᵛ? (|List| A) (|List| A') with sameᵛ? A A'
... | just p = just (|List|≡̂ p)
... | _      = nothing
sameᵛ? Empty Empty = just Empty≡̂
sameᵛ? (A ⇒ C) (A' ⇒ C') with sameᵛ? A A' | sameᶜ? C C'
... | just p | just q = just (p ⇒≡̂ q)
... | _      | _      = nothing
sameᵛ? ([ ρ ] A) ([ ρ' ] A') with ρ ≟ʳ ρ' | sameᵛ? A A'
... | yes r | just p = just ([ ≅ʳ⇒≡̂ r ]≡̂ p)
... | _     | _      = nothing
sameᵛ? _ _ = nothing

sameᶜ? (A ‼ ε) (A' ‼ ε') with sameᵛ? A A' | ε ≟ᵉ ε'
... | just p | yes e = just (p ‼≡̂ ≅ᵉ⇒≡̂ e)
... | _      | _     = nothing

-- A disjunction entailed by another: the same type, up to the
-- sameness of grades, and a grade
-- entailed (at the strength `full`) above its own. Of two each entailing the
-- other, the walk keeps the later.

Hᵈ : ∀ {Θ} → Hyps Θ → List (OVType Θ × RExp Θ) → Hyps Θ
Hᵈ Q ds = hyps (ets Q) (subᵥ Q) (ordᵣ Q) (ordₑ Q) ds

Okᵈ : ∀ {Θ} → Hyps Θ → (seen rest : List (OVType Θ × RExp Θ)) → OVType Θ × RExp Θ → Set
Okᵈ Q seen rest (A , ρ) = VarOK (Hᵈ Q (seen ++ rest)) A ρ

Aboveᵈ : ∀ {Θ} → Hyps Θ → OVType Θ → RExp Θ → List (OVType Θ × RExp Θ) → Set
Aboveᵈ {Θ} Q A ρ l =
  Σ[ A' ∈ OVType Θ ] Σ[ ρ' ∈ RExp Θ ] ((A' , ρ') ∈ l × A ≡̂ᵛ A' × Q ⊩ ρ ≾̂ᵣ ρ')

thereᵈ : ∀ {Θ} {Q : Hyps Θ} {A ρ x l} → Maybe (Aboveᵈ Q A ρ l) → Maybe (Aboveᵈ Q A ρ (x ∷ l))
thereᵈ (just (A' , ρ' , m , e , d)) = just (A' , ρ' , there m , e , d)
thereᵈ nothing                      = nothing

aboveᵈ? : ∀ {Θ} → (Q : Hyps Θ) → (A : OVType Θ) → (ρ : RExp Θ)
        → (l : List (OVType Θ × RExp Θ)) → Maybe (Aboveᵈ Q A ρ l)
aboveᵈ? Q A ρ []               = nothing
aboveᵈ? Q A ρ ((A' , ρ') ∷ l) with sameᵛ? A A'
... | nothing = thereᵈ (aboveᵈ? Q A ρ l)
... | just e with decideᵣ full Q ρ ρ'
...   | just d  = just (A' , ρ' , here refl , e , d)
...   | nothing = thereᵈ (aboveᵈ? Q A ρ l)

testᵈ : ∀ {Θ} → (Q : Hyps Θ) → (seen rest : List (OVType Θ × RExp Θ))
      → (p : OVType Θ × RExp Θ) → Maybe (Okᵈ Q seen rest p)
testᵈ Q seen rest (A , ρ) with aboveᵈ? (Hᵈ Q (seen ++ rest)) A ρ (seen ++ rest)
... | just (A' , ρ' , m , e , d) = just (hyp-ok m e d)
... | nothing           = nothing

walkᵈ : ∀ {Θ} → Hyps Θ → Hyps Θ
walkᵈ Q = Hᵈ Q (Walk.walk (Okᵈ Q) (testᵈ Q) [] (disj Q))

walkᵈ-⊩⁻ : ∀ {Θ} → (Q : Hyps Θ) → Q ⊩ᴴ walkᵈ Q
walkᵈ-⊩⁻ Q =
  ⊆ᴴ-⊩ (mk⊆ᴴ (λ m → m) (λ m → m) (λ m → m) (λ m → m)
             (Walk.walk-⊆ (Okᵈ Q) (testᵈ Q) [] (disj Q)))

walkᵈ-⊩ : ∀ {Θ} → (Q : Hyps Θ) → walkᵈ Q ⊩ᴴ Q
walkᵈ-⊩ {Θ} Q =
  mk⊩ᴴ⁼ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) hypᵣ hypₑ
        (Walk.walk-⊨ (Okᵈ Q) (testᵈ Q) (λ p → VarOK (walkᵈ Q) (proj₁ p) (proj₂ p))
                     close [] (disj Q) (λ ()) hyp-ok₀)
  where
    close : ∀ (seen rest : List (OVType Θ × RExp Θ)) {p} → Okᵈ Q seen rest p
          → (∀ {q} → q ∈ seen ++ rest → VarOK (walkᵈ Q) (proj₁ q) (proj₂ q))
          → VarOK (walkᵈ Q) (proj₁ p) (proj₂ p)
    close seen rest ok hs =
      ⊩ᴴ-VarOK (mk⊩ᴴ⁼ et-hyp (λ m → tvarₛ (hypᵗᵛ m)) hypᵣ hypₑ hs) ok

-- Every disjunction of the set settled, then those entailed by the
-- others dropped

settleᴴ : ∀ {Θ} → Hyps Θ → Hyps Θ
settleᴴ Q = walkᵈ (settleAll (disj Q) (split Q))

settleᴴ-⊩ : ∀ {Θ} → (Q : Hyps Θ) → settleᴴ Q ⊩ᴴ Q
settleᴴ-⊩ Q with settleAll-⊩ (disj Q) (split Q)
... | h , k =
      ⊩ᴴ-trans (walkᵈ-⊩ (settleAll (disj Q) (split Q)))
               (mk⊩ᴴ⁼ (⊩ets h) (⊩subᵥ h) (⊩ordᵣ⁼ h) (⊩ordₑ⁼ h) k)

settleᴴ-⊨ : ∀ {Θ} → (Q : Hyps Θ) → Q ⊨ᴴ settleᴴ Q
settleᴴ-⊨ Q =
  ⊨ᴴ-trans (λ δ h → settleAll-inst (disj Q) (split Q) δ (⊩disj h)
                      (mk⊩ᴴ (⊩ets h) (⊩subᵥ h) (⊩ordᵣ h) (⊩ordₑ h) (λ ())))
           (⊩ᴴ-⊨ᴴ (walkᵈ-⊩⁻ (settleAll (disj Q) (split Q))))

-- A subtyping or eternality atom entailed by the atoms kept before it
-- is dropped, those kept staying in place: entailment of such atoms is
-- reachability in a finite digraph.

Okᵖ : ∀ {n} → (seen rest : List (Fin n × Fin n)) → Fin n × Fin n → Set
Okᵖ seen rest p = seen ⊢ᵖ proj₁ p ≾ proj₂ p

reachᵖ? : ∀ {n} → (seen rest : List (Fin n × Fin n)) → (p : Fin n × Fin n)
        → Maybe (Okᵖ seen rest p)
reachᵖ? seen rest (α , β) = reach? seen α β

pruneᵛ : ∀ {n} → List (Fin n × Fin n) → List (Fin n × Fin n)
pruneᵛ = Walk.walk Okᵖ reachᵖ? []

-- The eternality atoms, along the subtyping atoms `l`

Okᴱ : ∀ {n} → List (Fin n × Fin n) → (seen rest : List (Fin n)) → Fin n → Set
Okᴱ l seen rest α = Etᴾ l seen α

etᴱ? : ∀ {n} → (l : List (Fin n × Fin n)) → (seen rest : List (Fin n)) → (α : Fin n)
     → Maybe (Okᴱ l seen rest α)
etᴱ? l seen rest α = etᴾ? l seen α

pruneᴱ : ∀ {n} → List (Fin n × Fin n) → List (Fin n) → List (Fin n)
pruneᴱ l = Walk.walk (Okᴱ l) (etᴱ? l) []

-- The set with its subtyping atoms `l` and its eternality atoms pruned
-- along them, the rest untouched

pruneᵀ-at : ∀ {Θ} → Hyps Θ → List (TyVar Θ × TyVar Θ) → Hyps Θ
pruneᵀ-at Q l = hyps (pruneᴱ l (ets Q)) l (ordᵣ Q) (ordₑ Q) (disj Q)

pruneᵀ-at-⊩ : ∀ {Θ} → (Q : Hyps Θ) → (l : List (TyVar Θ × TyVar Θ))
            → (∀ {α β} → (α , β) ∈ subᵥ Q → pruneᵀ-at Q l ⊩ᵗᵛ α ≾ β)
            → pruneᵀ-at Q l ⊩ᴴ Q
pruneᵀ-at-⊩ {Θ} Q l k =
  mk⊩ᴴ⁼ (Walk.walk-⊨ (Okᴱ l) (etᴱ? l) (λ α → pruneᵀ-at Q l ⊩ᴱ tvar α) close
                     [] (ets Q) (λ ()) et-hyp)
        (λ m → tvarₛ (k m)) hypᵣ hypₑ hyp-ok₀
  where
    close : ∀ (seen rest : List (TyVar Θ)) {α} → Okᴱ l seen rest α
          → (∀ {β} → β ∈ seen ++ rest → pruneᵀ-at Q l ⊩ᴱ tvar β)
          → pruneᵀ-at Q l ⊩ᴱ tvar α
    close seen rest w hs = Etᴾ-⊩' (λ q → q) (λ q → hs (∈-++⁺ˡ q)) w

pruneᵀ-at-⊩⁻ : ∀ {Θ} → (Q : Hyps Θ) → (l : List (TyVar Θ × TyVar Θ))
             → (∀ {p} → p ∈ l → p ∈ subᵥ Q) → Q ⊩ᴴ pruneᵀ-at Q l
pruneᵀ-at-⊩⁻ Q l k =
  ⊆ᴴ-⊩ (mk⊆ᴴ (Walk.walk-⊆ (Okᴱ l) (etᴱ? l) [] (ets Q)) k (λ m → m) (λ m → m) (λ m → m))

-- Both kinds of atom pruned

pruneᵀ : ∀ {Θ} → Hyps Θ → Hyps Θ
pruneᵀ Q = pruneᵀ-at Q (pruneᵛ (subᵥ Q))

pruneᵀ-⊩ : ∀ {Θ} → (Q : Hyps Θ) → pruneᵀ Q ⊩ᴴ Q
pruneᵀ-⊩ {Θ} Q =
  pruneᵀ-at-⊩ Q l
    (Walk.walk-⊨ Okᵖ reachᵖ? (λ p → pruneᵀ Q ⊩ᵗᵛ proj₁ p ≾ proj₂ p) close
                 [] (subᵥ Q) (λ ()) hypᵗᵛ)
  where
    l = pruneᵛ (subᵥ Q)

    close : ∀ (seen rest : List (TyVar Θ × TyVar Θ)) {p} → Okᵖ seen rest p
          → (∀ {q} → q ∈ seen ++ rest → pruneᵀ Q ⊩ᵗᵛ proj₁ q ≾ proj₂ q)
          → pruneᵀ Q ⊩ᵗᵛ proj₁ p ≾ proj₂ p
    close seen rest w hs = ⊢ᵖ-⊩' (λ q → hs (∈-++⁺ˡ q)) w

pruneᵀ-⊩⁻ : ∀ {Θ} → (Q : Hyps Θ) → Q ⊩ᴴ pruneᵀ Q
pruneᵀ-⊩⁻ Q = pruneᵀ-at-⊩⁻ Q (pruneᵛ (subᵥ Q)) (Walk.walk-⊆ Okᵖ reachᵖ? [] (subᵥ Q))

-- The eternality atoms pruned along the subtyping atoms of the set

pruneᴱᵀ : ∀ {Θ} → Hyps Θ → Hyps Θ
pruneᴱᵀ Q = pruneᵀ-at Q (subᵥ Q)

pruneᴱᵀ-⊩ : ∀ {Θ} → (Q : Hyps Θ) → pruneᴱᵀ Q ⊩ᴴ Q
pruneᴱᵀ-⊩ Q = pruneᵀ-at-⊩ Q (subᵥ Q) hypᵗᵛ

pruneᴱᵀ-⊩⁻ : ∀ {Θ} → (Q : Hyps Θ) → Q ⊩ᴴ pruneᴱᵀ Q
pruneᴱᵀ-⊩⁻ Q = pruneᵀ-at-⊩⁻ Q (subᵥ Q) (λ m → m)

-- A subtyping atom reachable from the atoms kept and those not yet
-- examined

Okᵛ : ∀ {n} → (seen rest : List (Fin n × Fin n)) → Fin n × Fin n → Set
Okᵛ seen rest p = seen ++ rest ⊢ᵖ proj₁ p ≾ proj₂ p

reachᵛ? : ∀ {n} → (seen rest : List (Fin n × Fin n)) → (p : Fin n × Fin n)
        → Maybe (Okᵛ seen rest p)
reachᵛ? seen rest (α , β) = reach? (seen ++ rest) α β

-- The subtyping atoms walked, the rest untouched

walkᵛ : ∀ {Θ} → Hyps Θ → Hyps Θ
walkᵛ Q = hyps (ets Q) (Walk.walk Okᵛ reachᵛ? [] (subᵥ Q)) (ordᵣ Q) (ordₑ Q) (disj Q)

walkᵛ-⊩⁻ : ∀ {Θ} → (Q : Hyps Θ) → Q ⊩ᴴ walkᵛ Q
walkᵛ-⊩⁻ Q =
  ⊆ᴴ-⊩ (mk⊆ᴴ (λ m → m) (Walk.walk-⊆ Okᵛ reachᵛ? [] (subᵥ Q)) (λ m → m) (λ m → m) (λ m → m))

walkᵛ-⊩ : ∀ {Θ} → (Q : Hyps Θ) → walkᵛ Q ⊩ᴴ Q
walkᵛ-⊩ {Θ} Q =
  mk⊩ᴴ⁼ et-hyp
        (λ m → tvarₛ (Walk.walk-⊨ Okᵛ reachᵛ? (λ p → walkᵛ Q ⊩ᵗᵛ proj₁ p ≾ proj₂ p) close
                                  [] (subᵥ Q) (λ ()) hypᵗᵛ m))
        hypᵣ hypₑ hyp-ok₀
  where
    close : ∀ (seen rest : List (TyVar Θ × TyVar Θ)) {p} → Okᵛ seen rest p
          → (∀ {q} → q ∈ seen ++ rest → walkᵛ Q ⊩ᵗᵛ proj₁ q ≾ proj₂ q)
          → walkᵛ Q ⊩ᵗᵛ proj₁ p ≾ proj₂ p
    close seen rest w hs = ⊢ᵖ-⊩' hs w

-- Grade orderings are pruned by a walk against a test of entailment:
-- one the test proves is dropped. The effect orderings are pruned
-- first, and the resource ones read with the effect ones kept.

-- The set of the grade orderings `seen`, with the effect orderings `lₑ`

Hʳ : ∀ {Θ} → List (EExp Θ × EExp Θ) → List (RExp Θ × RExp Θ) → Hyps Θ
Hʳ lₑ seen = hyps [] [] seen lₑ []

Hᵉ : ∀ {Θ} → List (EExp Θ × EExp Θ) → Hyps Θ
Hᵉ seen = hyps [] [] [] seen []

-- An ordering entailed by the orderings the test sees

Okʳ : ∀ {Θ} → List (EExp Θ × EExp Θ) → (seen rest : List (RExp Θ × RExp Θ))
    → RExp Θ × RExp Θ → Set
Okʳ lₑ seen rest p = Hʳ lₑ (seen ++ rest) ⊩ proj₁ p ≾̂ᵣ proj₂ p

Okᵉ : ∀ {Θ} → (seen rest : List (EExp Θ × EExp Θ)) → EExp Θ × EExp Θ → Set
Okᵉ seen rest p = Hᵉ (seen ++ rest) ⊩ proj₁ p ≾̂ₑ proj₂ p

Testʳ : Set
Testʳ = ∀ {Θ} → (lₑ : List (EExp Θ × EExp Θ)) → (seen rest : List (RExp Θ × RExp Θ))
      → (p : RExp Θ × RExp Θ) → Maybe (Okʳ lₑ seen rest p)

Testᵉ : Set
Testᵉ = ∀ {Θ} → (seen rest : List (EExp Θ × EExp Θ))
      → (p : EExp Θ × EExp Θ) → Maybe (Okᵉ seen rest p)

-- An ordering whose two sides are the same, or a repeat of one kept,
-- up to the sameness of its sides

repeatʳ? : Testʳ
repeatʳ? lₑ seen rest (ρ , ρ') with ρ ≟ʳ ρ'
... | yes e = just (eqᵣ (≅ʳ⇒≡̂ e))
... | no _ with memʳ? (ρ , ρ') seen
...   | just m  = just (memʳ-⊩ (λ m' → hypᵣ (∈-++⁺ˡ m')) m)
...   | nothing = nothing

repeatᵉ? : Testᵉ
repeatᵉ? seen rest (ε , ε') with ε ≟ᵉ ε'
... | yes e = just (eqₑ (≅ᵉ⇒≡̂ e))
... | no _ with memᵉ? (ε , ε') seen
...   | just m  = just (memᵉ-⊩ (λ m' → hypₑ (∈-++⁺ˡ m')) m)
...   | nothing = nothing

-- An ordering entailed at the strength `full` by those kept and
-- those not yet examined

entailsʳ? : Testʳ
entailsʳ? lₑ seen rest (ρ , ρ') = decideᵣ full (Hʳ lₑ (seen ++ rest)) ρ ρ'

entailsᵉ? : Testᵉ
entailsᵉ? seen rest (ε , ε') = decideₑ full (Hᵉ (seen ++ rest)) ε ε'

module Pruneᴼ (testʳ : Testʳ) (testᵉ : Testᵉ) where

  pruneᴼᵉ : ∀ {Θ} → List (EExp Θ × EExp Θ) → List (EExp Θ × EExp Θ)
  pruneᴼᵉ = Walk.walk Okᵉ testᵉ []

  pruneᴼʳ : ∀ {Θ} → List (EExp Θ × EExp Θ) → List (RExp Θ × RExp Θ)
          → List (RExp Θ × RExp Θ)
  pruneᴼʳ lₑ = Walk.walk (Okʳ lₑ) (testʳ lₑ) []

  -- The grade orderings pruned, the rest untouched. `pruneᴼ-at Q lₑ` is
  -- the set with its effect orderings `lₑ` and its resource orderings
  -- pruned against them.

  pruneᴼ-at : ∀ {Θ} → Hyps Θ → List (EExp Θ × EExp Θ) → Hyps Θ
  pruneᴼ-at Q lₑ = hyps (ets Q) (subᵥ Q) (pruneᴼʳ lₑ (ordᵣ Q)) lₑ (disj Q)

  pruneᴼ : ∀ {Θ} → Hyps Θ → Hyps Θ
  pruneᴼ Q = pruneᴼ-at Q (pruneᴼᵉ (ordₑ Q))

  pruneᴼ-⊩⁻ : ∀ {Θ} → (Q : Hyps Θ) → Q ⊩ᴴ pruneᴼ Q
  pruneᴼ-⊩⁻ Q =
    ⊆ᴴ-⊩ (mk⊆ᴴ (λ m → m) (λ m → m)
               (Walk.walk-⊆ (Okʳ lₑ) (testʳ lₑ) [] (ordᵣ Q))
               (Walk.walk-⊆ Okᵉ testᵉ [] (ordₑ Q)) (λ m → m))
    where lₑ = pruneᴼᵉ (ordₑ Q)

  pruneᴼ-⊩ : ∀ {Θ} → (Q : Hyps Θ) → pruneᴼ Q ⊩ᴴ Q
  pruneᴼ-⊩ {Θ} Q =
    mk⊩ᴴ⁼ et-hyp (λ m → tvarₛ (hypᵗᵛ m))
          (Walk.walk-⊨ (Okʳ lₑ) (testʳ lₑ) (λ p → pruneᴼ Q ⊩ proj₁ p ≾̂ᵣ proj₂ p)
                       closeʳ [] (ordᵣ Q) (λ ()) hypᵣ)
          (Walk.walk-⊨ Okᵉ testᵉ (λ p → pruneᴼ Q ⊩ proj₁ p ≾̂ₑ proj₂ p)
                       closeᵉ [] (ordₑ Q) (λ ()) hypₑ)
          hyp-ok₀
    where
      lₑ = pruneᴼᵉ (ordₑ Q)

      closeʳ : ∀ (seen rest : List (RExp Θ × RExp Θ)) {p} → Okʳ lₑ seen rest p
             → (∀ {q} → q ∈ seen ++ rest → pruneᴼ Q ⊩ proj₁ q ≾̂ᵣ proj₂ q)
             → pruneᴼ Q ⊩ proj₁ p ≾̂ᵣ proj₂ p
      closeʳ seen rest d hs =
        ⊩ᴴ-≾ᵣ (mk⊩ᴴ⁼ (λ ()) (λ ()) hs hypₑ (λ ())) d

      closeᵉ : ∀ (seen rest : List (EExp Θ × EExp Θ)) {p} → Okᵉ seen rest p
             → (∀ {q} → q ∈ seen ++ rest → pruneᴼ Q ⊩ proj₁ q ≾̂ₑ proj₂ q)
             → pruneᴼ Q ⊩ proj₁ p ≾̂ₑ proj₂ p
      closeᵉ seen rest d hs =
        ⊩ᴴ-≾ₑ (mk⊩ᴴ⁼ (λ ()) (λ ()) (λ ()) hs (λ ())) d

module Repeats  = Pruneᴼ repeatʳ?  repeatᵉ?
module Entailed = Pruneᴼ entailsʳ? entailsᵉ?

prune : ∀ {Θ} → Hyps Θ → Hyps Θ
prune Q = Repeats.pruneᴼ (pruneᵀ Q)

prune-⊩ : ∀ {Θ} → (Q : Hyps Θ) → prune Q ⊩ᴴ Q
prune-⊩ Q = ⊩ᴴ-trans (Repeats.pruneᴼ-⊩ (pruneᵀ Q)) (pruneᵀ-⊩ Q)

prune-⊩⁻ : ∀ {Θ} → (Q : Hyps Θ) → Q ⊩ᴴ prune Q
prune-⊩⁻ Q = ⊩ᴴ-trans (pruneᵀ-⊩⁻ Q) (Repeats.pruneᴼ-⊩⁻ (pruneᵀ Q))

order : ∀ {Θ} → Hyps Θ → Hyps Θ
order Q = hyps (ets Q) (subᵥ Q) (sortᴼ _≺ᵣ_ (ordᵣ Q)) (sortᴼ _≺ₑ_ (ordₑ Q)) (disj Q)

order-⊩ : ∀ {Θ} → (Q : Hyps Θ) → order Q ⊩ᴴ Q
order-⊩ Q =
  ⊆ᴴ-⊩ (mk⊆ᴴ (λ m → m) (λ m → m) (sortᴼ-⊇ _≺ᵣ_ (ordᵣ Q)) (sortᴼ-⊇ _≺ₑ_ (ordₑ Q)) (λ m → m))

order-⊩⁻ : ∀ {Θ} → (Q : Hyps Θ) → Q ⊩ᴴ order Q
order-⊩⁻ Q =
  ⊆ᴴ-⊩ (mk⊆ᴴ (λ m → m) (λ m → m) (sortᴼ-⊆ _≺ᵣ_ (ordᵣ Q)) (sortᴼ-⊆ _≺ₑ_ (ordₑ Q)) (λ m → m))

simplify : ∀ {Θ} → Hyps Θ → Hyps Θ
simplify Q = order (prune (settleᴴ (canonᴴ Q)))

-- The simplified set entails the set, and every closed instance of the
-- set is one of it

simplify-⊩ : ∀ {Θ} → (Q : Hyps Θ) → simplify Q ⊩ᴴ Q
simplify-⊩ Q =
  ⊩ᴴ-trans (order-⊩ (prune (settleᴴ (canonᴴ Q))))
    (⊩ᴴ-trans (prune-⊩ (settleᴴ (canonᴴ Q)))
      (⊩ᴴ-trans (settleᴴ-⊩ (canonᴴ Q)) (canonᴴ-⊩ Q)))

simplify-⊨ : ∀ {Θ} → (Q : Hyps Θ) → Q ⊨ᴴ simplify Q
simplify-⊨ Q =
  ⊨ᴴ-trans (⊩ᴴ-⊨ᴴ (canonᴴ-⊩⁻ Q))
    (⊨ᴴ-trans (settleᴴ-⊨ (canonᴴ Q))
      (⊩ᴴ-⊨ᴴ (⊩ᴴ-trans (prune-⊩⁻ (settleᴴ (canonᴴ Q)))
                       (order-⊩⁻ (prune (settleᴴ (canonᴴ Q)))))))

-- The disjunctions settled, then every subtyping atom entailed by
-- those kept and those not yet examined dropped, the eternality atoms
-- pruned along those left, and every grade ordering entailed by those
-- kept and those not yet examined dropped

trim : ∀ {Θ} → Hyps Θ → Hyps Θ
trim Q = Entailed.pruneᴼ (pruneᴱᵀ (walkᵛ (settleᴴ Q)))

trim-⊩ : ∀ {Θ} → (Q : Hyps Θ) → trim Q ⊩ᴴ Q
trim-⊩ Q =
  ⊩ᴴ-trans (Entailed.pruneᴼ-⊩ (pruneᴱᵀ (walkᵛ (settleᴴ Q))))
    (⊩ᴴ-trans (pruneᴱᵀ-⊩ (walkᵛ (settleᴴ Q)))
      (⊩ᴴ-trans (walkᵛ-⊩ (settleᴴ Q)) (settleᴴ-⊩ Q)))

trim-⊨ : ∀ {Θ} → (Q : Hyps Θ) → Q ⊨ᴴ trim Q
trim-⊨ Q =
  ⊨ᴴ-trans (settleᴴ-⊨ Q)
    (⊩ᴴ-⊨ᴴ (⊩ᴴ-trans (walkᵛ-⊩⁻ (settleᴴ Q))
             (⊩ᴴ-trans (pruneᴱᵀ-⊩⁻ (walkᵛ (settleᴴ Q)))
                       (Entailed.pruneᴼ-⊩⁻ (pruneᴱᵀ (walkᵛ (settleᴴ Q)))))))

-- Trimming a whole report, as an elimination step that instantiates
-- no unknown

trimElim : ∀ {Θ} → (C : OCType Θ) → (Q : Hyps Θ) → Elim C Q
trimElim C Q =
  mkElim C (trim Q) idˢ (subst (C ≡̂ᶜ_) (sym ([id]ᶜ C)) (≡̂ᶜ-refl C))
         (trim-⊩ Q) (trim-⊨ Q) (λ δ h → <:̂ᶜ-refl (C [ δ ]ᶜ))
