------------------------------------------------------------------
-- Sufficiently annotated raw terms                               --
--                                                                --
-- The condition of the theorem that inference on such a term is  --
-- never `stuck`. It constrains the operation clauses of          --
-- handlers only: the bodies `H op` of every `handle`, and        --
-- everything within them, nested handlers included. There,       --
--                                                                --
--   A1  every λ annotates its argument: `lam[ A ] M`, not        --
--       `lam M`;                                                 --
--   A2  every `absurd V` is the immediate subject of a           --
--       computation annotation, `absurd V ⦂ᶜ C`;                 --
--   A3  every `if` and every nested `handle` is the immediate    --
--       subject of a computation annotation:                     --
--       `(if V `then M `else N) ⦂ᶜ C`,                           --
--       `(handle M `with H `in N) ⦂ᶜ C`.                         --
--                                                                --
-- Outside the clauses nothing is required, so a handler-free     --
-- term is sufficiently annotated. The handled computation and    --
-- the continuation of a `handle` sit where the `handle` sits.    --
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import TypeInference.Scopes

module TypeInference.Raw.SufficientlyAnnotated (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops

open import TypeInference.OpenSyntax.Subst S using (Subst)
open import TypeInference.Raw.Syntax S
open import TypeInference.Raw.Subst S using (_[_]ᴿᵛ; _[_]ᴿᶜ)
open import TypeInference.SolverImpl.Enum S using (OpEnum; AllOp; []; _∷_; all-lookup)

-- Where a subterm sits: outside every operation clause, or inside one

data Site : Set where
  outside inside : Site

-- A bare `lam`, `absurd`, `if` or `handle` is allowed outside the
-- clauses only

Bare : Site → Set
Bare outside = ⊤
Bare inside  = ⊥

-- Sufficient annotation at a site

mutual

  Annotatedᵛ : ∀ {Θ n} → Site → RawV Θ n → Set
  Annotatedᵛ s ⦉ V , W ⦊     = Annotatedᵛ s V × Annotatedᵛ s W
  Annotatedᵛ s (lam M)      = Bare s × Annotatedᶜ s M
  Annotatedᵛ s (lam[ A ] M) = Annotatedᶜ s M
  Annotatedᵛ s (V ⦂ᵛ A)     = Annotatedᵛ s V
  Annotatedᵛ s _            = ⊤

  Annotatedᶜ : ∀ {Θ n} → Site → RawC Θ n → Set
  Annotatedᶜ s (return V)               = Annotatedᵛ s V
  Annotatedᶜ s (M ⨟ N)                  = Annotatedᶜ s M × Annotatedᶜ s N
  Annotatedᶜ s (V · W)                  = Annotatedᵛ s V × Annotatedᵛ s W
  Annotatedᶜ s (match V `in M)          = Annotatedᵛ s V × Annotatedᶜ s M
  Annotatedᶜ s (absurd V)               = Bare s × Annotatedᵛ s V
  Annotatedᶜ s (if V `then M `else N)   =
    Bare s × Annotatedᵛ s V × Annotatedᶜ s M × Annotatedᶜ s N
  Annotatedᶜ s (perform op V M)         = Annotatedᵛ s V × Annotatedᶜ s M
  Annotatedᶜ s (delay τ M)              = Annotatedᶜ s M
  Annotatedᶜ s (handle M `with H `in N) =
    Bare s × Annotatedᶜ s M × ((op : Op) → Annotatedᶜ inside (H op)) × Annotatedᶜ s N
  Annotatedᶜ s (unbox i N)              = Annotatedᶜ s N
  Annotatedᶜ s (box ρ V N)              = Annotatedᵛ s V × Annotatedᶜ s N
  -- the places a bare `absurd`, `if` or `handle` is accepted
  Annotatedᶜ s (absurd V ⦂ᶜ C)          = Annotatedᵛ s V
  Annotatedᶜ s ((if V `then M `else N) ⦂ᶜ C) =
    Annotatedᵛ s V × Annotatedᶜ s M × Annotatedᶜ s N
  Annotatedᶜ s ((handle M `with H `in N) ⦂ᶜ C) =
    Annotatedᶜ s M × ((op : Op) → Annotatedᶜ inside (H op)) × Annotatedᶜ s N
  Annotatedᶜ s (M ⦂ᶜ C)                 = Annotatedᶜ s M

-- A program is sufficiently annotated when it is at the outermost site

SufficientlyAnnotatedᵛ : ∀ {Θ n} → RawV Θ n → Set
SufficientlyAnnotatedᵛ = Annotatedᵛ outside

SufficientlyAnnotated : ∀ {Θ n} → RawC Θ n → Set
SufficientlyAnnotated = Annotatedᶜ outside

------------------------------------------------------------------
-- A handler-free term is sufficiently annotated

mutual

  handlerFree→annotatedᵛ : ∀ {Θ n} → (V : RawV Θ n)
                         → HandlerFreeᵛ V → SufficientlyAnnotatedᵛ V
  handlerFree→annotatedᵛ (var i)      h       = tt
  handlerFree→annotatedᵛ (const B c)  h       = tt
  handlerFree→annotatedᵛ ⋆            h       = tt
  handlerFree→annotatedᵛ true         h       = tt
  handlerFree→annotatedᵛ false        h       = tt
  handlerFree→annotatedᵛ ⦉ V , W ⦊     (h , k) =
    handlerFree→annotatedᵛ V h , handlerFree→annotatedᵛ W k
  handlerFree→annotatedᵛ (lam M)      h       = tt , handlerFree→sufficientlyAnnotated M h
  handlerFree→annotatedᵛ (lam[ A ] M) h       = handlerFree→sufficientlyAnnotated M h
  handlerFree→annotatedᵛ (V ⦂ᵛ A)     h       = handlerFree→annotatedᵛ V h

  handlerFree→sufficientlyAnnotated : ∀ {Θ n} → (M : RawC Θ n)
                                    → HandlerFreeᶜ M → SufficientlyAnnotated M
  handlerFree→sufficientlyAnnotated (return V)               h           =
    handlerFree→annotatedᵛ V h
  handlerFree→sufficientlyAnnotated (M ⨟ N)                  (h , k)     =
    handlerFree→sufficientlyAnnotated M h , handlerFree→sufficientlyAnnotated N k
  handlerFree→sufficientlyAnnotated (V · W)                  (h , k)     =
    handlerFree→annotatedᵛ V h , handlerFree→annotatedᵛ W k
  handlerFree→sufficientlyAnnotated (match V `in M)          (h , k)     =
    handlerFree→annotatedᵛ V h , handlerFree→sufficientlyAnnotated M k
  handlerFree→sufficientlyAnnotated (absurd V)               h           =
    tt , handlerFree→annotatedᵛ V h
  handlerFree→sufficientlyAnnotated (if V `then M `else N)   (h , k , l) =
    tt , handlerFree→annotatedᵛ V h , handlerFree→sufficientlyAnnotated M k
                                    , handlerFree→sufficientlyAnnotated N l
  handlerFree→sufficientlyAnnotated (perform op V M)         (h , k)     =
    handlerFree→annotatedᵛ V h , handlerFree→sufficientlyAnnotated M k
  handlerFree→sufficientlyAnnotated (delay τ M)              h           =
    handlerFree→sufficientlyAnnotated M h
  handlerFree→sufficientlyAnnotated (handle M `with H `in N) ()
  handlerFree→sufficientlyAnnotated (unbox i N)              h           =
    handlerFree→sufficientlyAnnotated N h
  handlerFree→sufficientlyAnnotated (box ρ V N)              (h , k)     =
    handlerFree→annotatedᵛ V h , handlerFree→sufficientlyAnnotated N k
  handlerFree→sufficientlyAnnotated (absurd V ⦂ᶜ C)          h           =
    handlerFree→annotatedᵛ V h
  handlerFree→sufficientlyAnnotated ((if V `then M `else N) ⦂ᶜ C) (h , k , l) =
    handlerFree→annotatedᵛ V h , handlerFree→sufficientlyAnnotated M k
                               , handlerFree→sufficientlyAnnotated N l
  handlerFree→sufficientlyAnnotated ((handle M `with H `in N) ⦂ᶜ C) ()
  -- the other subjects of an annotation, one clause each
  handlerFree→sufficientlyAnnotated (M@(return _) ⦂ᶜ C) h =
    handlerFree→sufficientlyAnnotated M h
  handlerFree→sufficientlyAnnotated (M@(_ ⨟ _) ⦂ᶜ C) h =
    handlerFree→sufficientlyAnnotated M h
  handlerFree→sufficientlyAnnotated (M@(_ · _) ⦂ᶜ C) h =
    handlerFree→sufficientlyAnnotated M h
  handlerFree→sufficientlyAnnotated (M@(match _ `in _) ⦂ᶜ C) h =
    handlerFree→sufficientlyAnnotated M h
  handlerFree→sufficientlyAnnotated (M@(perform _ _ _) ⦂ᶜ C) h =
    handlerFree→sufficientlyAnnotated M h
  handlerFree→sufficientlyAnnotated (M@(delay _ _) ⦂ᶜ C) h =
    handlerFree→sufficientlyAnnotated M h
  handlerFree→sufficientlyAnnotated (M@(unbox _ _) ⦂ᶜ C) h =
    handlerFree→sufficientlyAnnotated M h
  handlerFree→sufficientlyAnnotated (M@(box _ _ _) ⦂ᶜ C) h =
    handlerFree→sufficientlyAnnotated M h
  handlerFree→sufficientlyAnnotated (M@(_ ⦂ᶜ _) ⦂ᶜ C) h =
    handlerFree→sufficientlyAnnotated M h

------------------------------------------------------------------
-- Stability under substitution: annotations are substituted into,
-- never removed

mutual

  annotated-[]ᴿᵛ : ∀ {Θ Θ' n s} {σ : Subst Θ Θ'} → (V : RawV Θ n)
                 → Annotatedᵛ s V → Annotatedᵛ s (V [ σ ]ᴿᵛ)
  annotated-[]ᴿᵛ (var i)      a       = tt
  annotated-[]ᴿᵛ (const B c)  a       = tt
  annotated-[]ᴿᵛ ⋆            a       = tt
  annotated-[]ᴿᵛ true         a       = tt
  annotated-[]ᴿᵛ false        a       = tt
  annotated-[]ᴿᵛ ⦉ V , W ⦊     (a , b) = annotated-[]ᴿᵛ V a , annotated-[]ᴿᵛ W b
  annotated-[]ᴿᵛ (lam M)      (a , b) = a , annotated-[]ᴿᶜ M b
  annotated-[]ᴿᵛ (lam[ A ] M) a       = annotated-[]ᴿᶜ M a
  annotated-[]ᴿᵛ (V ⦂ᵛ A)     a       = annotated-[]ᴿᵛ V a

  annotated-[]ᴿᶜ : ∀ {Θ Θ' n s} {σ : Subst Θ Θ'} → (M : RawC Θ n)
                 → Annotatedᶜ s M → Annotatedᶜ s (M [ σ ]ᴿᶜ)
  annotated-[]ᴿᶜ (return V)               a           = annotated-[]ᴿᵛ V a
  annotated-[]ᴿᶜ (M ⨟ N)                  (a , b)     =
    annotated-[]ᴿᶜ M a , annotated-[]ᴿᶜ N b
  annotated-[]ᴿᶜ (V · W)                  (a , b)     =
    annotated-[]ᴿᵛ V a , annotated-[]ᴿᵛ W b
  annotated-[]ᴿᶜ (match V `in M)          (a , b)     =
    annotated-[]ᴿᵛ V a , annotated-[]ᴿᶜ M b
  annotated-[]ᴿᶜ (absurd V)               (a , b)     = a , annotated-[]ᴿᵛ V b
  annotated-[]ᴿᶜ (if V `then M `else N)   (a , b , c , d) =
    a , annotated-[]ᴿᵛ V b , annotated-[]ᴿᶜ M c , annotated-[]ᴿᶜ N d
  annotated-[]ᴿᶜ (perform op V M)         (a , b)     =
    annotated-[]ᴿᵛ V a , annotated-[]ᴿᶜ M b
  annotated-[]ᴿᶜ (delay τ M)              a           = annotated-[]ᴿᶜ M a
  annotated-[]ᴿᶜ (handle M `with H `in N) (a , b , c , d) =
    a , annotated-[]ᴿᶜ M b , (λ op → annotated-[]ᴿᶜ (H op) (c op)) , annotated-[]ᴿᶜ N d
  annotated-[]ᴿᶜ (unbox i N)              a           = annotated-[]ᴿᶜ N a
  annotated-[]ᴿᶜ (box ρ V N)              (a , b)     =
    annotated-[]ᴿᵛ V a , annotated-[]ᴿᶜ N b
  annotated-[]ᴿᶜ (absurd V ⦂ᶜ C)          a           = annotated-[]ᴿᵛ V a
  annotated-[]ᴿᶜ ((if V `then M `else N) ⦂ᶜ C) (a , b , c) =
    annotated-[]ᴿᵛ V a , annotated-[]ᴿᶜ M b , annotated-[]ᴿᶜ N c
  annotated-[]ᴿᶜ ((handle M `with H `in N) ⦂ᶜ C) (a , b , c) =
    annotated-[]ᴿᶜ M a , (λ op → annotated-[]ᴿᶜ (H op) (b op)) , annotated-[]ᴿᶜ N c
  -- the other subjects of an annotation, one clause each
  annotated-[]ᴿᶜ (M@(return _) ⦂ᶜ C) a = annotated-[]ᴿᶜ M a
  annotated-[]ᴿᶜ (M@(_ ⨟ _) ⦂ᶜ C) a = annotated-[]ᴿᶜ M a
  annotated-[]ᴿᶜ (M@(_ · _) ⦂ᶜ C) a = annotated-[]ᴿᶜ M a
  annotated-[]ᴿᶜ (M@(match _ `in _) ⦂ᶜ C) a = annotated-[]ᴿᶜ M a
  annotated-[]ᴿᶜ (M@(perform _ _ _) ⦂ᶜ C) a = annotated-[]ᴿᶜ M a
  annotated-[]ᴿᶜ (M@(delay _ _) ⦂ᶜ C) a = annotated-[]ᴿᶜ M a
  annotated-[]ᴿᶜ (M@(unbox _ _) ⦂ᶜ C) a = annotated-[]ᴿᶜ M a
  annotated-[]ᴿᶜ (M@(box _ _ _) ⦂ᶜ C) a = annotated-[]ᴿᶜ M a
  annotated-[]ᴿᶜ (M@(_ ⦂ᶜ _) ⦂ᶜ C) a = annotated-[]ᴿᶜ M a

sufficientlyAnnotated-[]ᴿᶜ : ∀ {Θ Θ' n} {σ : Subst Θ Θ'} → (M : RawC Θ n)
                           → SufficientlyAnnotated M
                           → SufficientlyAnnotated (M [ σ ]ᴿᶜ)
sufficientlyAnnotated-[]ᴿᶜ = annotated-[]ᴿᶜ

------------------------------------------------------------------
-- Deciding it, given an enumeration of the operations

module _ (opEnum : OpEnum) where

  open OpEnum opEnum

  private

    bare? : (s : Site) → Dec (Bare s)
    bare? outside = yes tt
    bare? inside  = no (λ ())

    all? : {P : Op → Set} → ((op : Op) → Dec (P op)) → (xs : List Op)
         → Dec (AllOp P xs)
    all? d []       = yes []
    all? d (x ∷ xs) with d x | all? d xs
    ... | yes p | yes ps = yes (p ∷ ps)
    ... | no ¬p | _      = no (λ { (p ∷ _) → ¬p p })
    ... | yes _ | no ¬ps = no (λ { (_ ∷ ps) → ¬ps ps })

    all-of : {P : Op → Set} → ((op : Op) → P op) → (xs : List Op) → AllOp P xs
    all-of f []       = []
    all-of f (x ∷ xs) = f x ∷ all-of f xs

    ∀op? : {P : Op → Set} → ((op : Op) → Dec (P op)) → Dec ((op : Op) → P op)
    ∀op? d with all? d ops
    ... | yes a = yes (λ op → all-lookup a (complete op))
    ... | no ¬a = no (λ f → ¬a (all-of f ops))

  mutual

    annotatedᵛ? : ∀ {Θ n} → (s : Site) → (V : RawV Θ n) → Dec (Annotatedᵛ s V)
    annotatedᵛ? s (var i)      = yes tt
    annotatedᵛ? s (const B c)  = yes tt
    annotatedᵛ? s ⋆            = yes tt
    annotatedᵛ? s true         = yes tt
    annotatedᵛ? s false        = yes tt
    annotatedᵛ? s ⦉ V , W ⦊     = annotatedᵛ? s V ×-dec annotatedᵛ? s W
    annotatedᵛ? s (lam M)      = bare? s ×-dec annotatedᶜ? s M
    annotatedᵛ? s (lam[ A ] M) = annotatedᶜ? s M
    annotatedᵛ? s (V ⦂ᵛ A)     = annotatedᵛ? s V

    annotatedᶜ? : ∀ {Θ n} → (s : Site) → (M : RawC Θ n) → Dec (Annotatedᶜ s M)
    annotatedᶜ? s (return V)               = annotatedᵛ? s V
    annotatedᶜ? s (M ⨟ N)                  = annotatedᶜ? s M ×-dec annotatedᶜ? s N
    annotatedᶜ? s (V · W)                  = annotatedᵛ? s V ×-dec annotatedᵛ? s W
    annotatedᶜ? s (match V `in M)          = annotatedᵛ? s V ×-dec annotatedᶜ? s M
    annotatedᶜ? s (absurd V)               = bare? s ×-dec annotatedᵛ? s V
    annotatedᶜ? s (if V `then M `else N)   =
      bare? s ×-dec (annotatedᵛ? s V ×-dec (annotatedᶜ? s M ×-dec annotatedᶜ? s N))
    annotatedᶜ? s (perform op V M)         = annotatedᵛ? s V ×-dec annotatedᶜ? s M
    annotatedᶜ? s (delay τ M)              = annotatedᶜ? s M
    annotatedᶜ? s (handle M `with H `in N) =
      bare? s ×-dec
        (annotatedᶜ? s M ×-dec (∀op? (λ op → annotatedᶜ? inside (H op)) ×-dec annotatedᶜ? s N))
    annotatedᶜ? s (unbox i N)              = annotatedᶜ? s N
    annotatedᶜ? s (box ρ V N)              = annotatedᵛ? s V ×-dec annotatedᶜ? s N
    annotatedᶜ? s (absurd V ⦂ᶜ C)          = annotatedᵛ? s V
    annotatedᶜ? s ((if V `then M `else N) ⦂ᶜ C) =
      annotatedᵛ? s V ×-dec (annotatedᶜ? s M ×-dec annotatedᶜ? s N)
    annotatedᶜ? s ((handle M `with H `in N) ⦂ᶜ C) =
      annotatedᶜ? s M ×-dec (∀op? (λ op → annotatedᶜ? inside (H op)) ×-dec annotatedᶜ? s N)
    -- the other subjects of an annotation, one clause each
    annotatedᶜ? s (M@(return _) ⦂ᶜ C) = annotatedᶜ? s M
    annotatedᶜ? s (M@(_ ⨟ _) ⦂ᶜ C) = annotatedᶜ? s M
    annotatedᶜ? s (M@(_ · _) ⦂ᶜ C) = annotatedᶜ? s M
    annotatedᶜ? s (M@(match _ `in _) ⦂ᶜ C) = annotatedᶜ? s M
    annotatedᶜ? s (M@(perform _ _ _) ⦂ᶜ C) = annotatedᶜ? s M
    annotatedᶜ? s (M@(delay _ _) ⦂ᶜ C) = annotatedᶜ? s M
    annotatedᶜ? s (M@(unbox _ _) ⦂ᶜ C) = annotatedᶜ? s M
    annotatedᶜ? s (M@(box _ _ _) ⦂ᶜ C) = annotatedᶜ? s M
    annotatedᶜ? s (M@(_ ⦂ᶜ _) ⦂ᶜ C) = annotatedᶜ? s M

  sufficientlyAnnotatedᵛ? : ∀ {Θ n} → (V : RawV Θ n) → Dec (SufficientlyAnnotatedᵛ V)
  sufficientlyAnnotatedᵛ? = annotatedᵛ? outside

  sufficientlyAnnotated? : ∀ {Θ n} → (M : RawC Θ n) → Dec (SufficientlyAnnotated M)
  sufficientlyAnnotated? = annotatedᶜ? outside
