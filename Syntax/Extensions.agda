-- {-# OPTIONS --allow-unsolved-metas #-} -- (remove)

------------------------
-- Context extensions --
------------------------

open import Syntax.Grades

module Syntax.Extensions (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product
open import Data.Empty
open import Data.Sum

open import Relation.Binary.Core -- Remove?
open import Relation.Binary.Definitions -- Remove?
open import Relation.Nullary -- Remove?
open import Relation.Binary.PropositionalEquality as Eq hiding ( [_] )
open Eq.≡-Reasoning

--open import Syntax.Extensions.Raw (Grades) -- Remove

open import Syntax.Contexts (Grades)
open import Syntax.Renamings (Grades)

-- Context extension

data Ext : Ctx → R → Ctx → Set where
  id-ext : ∀ {Γ} → Ext Γ uᵣ Γ
  ∷-ext  : ∀ {Γ Γ' A ρ} → Ext Γ ρ Γ' → Ext Γ ρ (Γ' ∷ A)
  ⟨⟩-ext : ∀ {Γ Γ' ρ ρ'} → Ext Γ ρ Γ' → Ext Γ (ρ ·ᵣ ρ') (Γ' ⟨ ρ' ⟩)

-- Inversion lemmas

inv-ext-∷ : ∀ {Γ ρ Γ' A}
          → (e : Ext Γ ρ (Γ' ∷ A))
          → ( Σ[ eq-grades ∈ (uᵣ ≡ ρ) ]
                 Σ[ eq-ctxs ∈ (Γ ≡ (Γ' ∷ A)) ]
                   (subst₂ (λ gr ctx → Ext Γ gr ctx) eq-grades eq-ctxs id-ext ≡ e))
          ⊎ (Ext Γ ρ Γ')
inv-ext-∷ id-ext    = inj₁ (refl , refl , refl)
inv-ext-∷ (∷-ext e) = inj₂ e

inv-ext-⟨⟩ : ∀ {Γ ρ Γ' ρ'} 
           → (e : Ext Γ ρ (Γ' ⟨ ρ' ⟩)) 
           → (Σ[ eq-grades ∈ (uᵣ ≡ ρ) ]
                 Σ[ eq-ctxs ∈ (Γ ≡ Γ' ⟨ ρ' ⟩) ]
                   (subst₂ (λ gr ctx → Ext Γ gr ctx) eq-grades eq-ctxs id-ext ≡ e))
             ⊎ (Σ[ ρ'' ∈ R ] (Ext Γ ρ'' Γ' × (ρ ≡ ρ'' ·ᵣ ρ' )))
inv-ext-⟨⟩ id-ext     = inj₁ (refl , refl , refl)
inv-ext-⟨⟩ (⟨⟩-ext e) = inj₂ (_ , e , refl)

-- Subcontexts cannot extend their supercontexts

ext-decrease-contradiction-[] : ∀ {Γ ρ} → Γ ≢ [] → Ext Γ ρ [] → ⊥
ext-decrease-contradiction-[] {Γ} {ρ} p id-ext = p refl

ext-decrease-contradiction : ∀ {Γ Γ' ρ} → Γ' ≢ [] → Ext (Γ ++ᶜ Γ') ρ Γ → ⊥
ext-decrease-contradiction {[]} {Γ'} {ρ} p e rewrite ++ᶜ-identityˡ {Γ'} =
  ext-decrease-contradiction-[] p e
ext-decrease-contradiction {Γ ∷ A} {Γ'} {ρ} p e with inv-ext-∷ e
... | inj₁ (q , r , u) =
  p (++ᶜ-identityʳ-unique (sym r))
... | inj₂ e' rewrite ++ᶜ-assoc Γ ([] ∷ A) Γ' =
  ext-decrease-contradiction (λ q → {!!}) e'
ext-decrease-contradiction {Γ ⟨ ρ' ⟩} {Γ'} {ρ} p e with inv-ext-⟨⟩ e
... | inj₁ (q , r , u) =
  p (++ᶜ-identityʳ-unique (sym r))
... | inj₂ (ρ'' , e' , q) rewrite ++ᶜ-assoc Γ ([] ⟨ ρ' ⟩) Γ' =
  ext-decrease-contradiction {!!} e'

--

ext-≡-grade : ∀ {Γ Γ' ρ ρ'} → Ext Γ ρ Γ' → ρ ≡ ρ' → Ext Γ ρ' Γ'
ext-≡-grade e refl = e

-- Concatenation extends a context

ext-++ᶜ : ∀ {Γ Γ'} → Ext Γ (ctx-grade Γ') (Γ ++ᶜ Γ')
ext-++ᶜ {Γ} {[]} = id-ext
ext-++ᶜ {Γ} {Γ' ∷ A} = ∷-ext ext-++ᶜ
ext-++ᶜ {Γ} {Γ' ⟨ ρ ⟩} = ⟨⟩-ext ext-++ᶜ

-- Empty context always extends other contexts

ext-[] : ∀ {Γ} → Ext [] (ctx-grade Γ) Γ
ext-[] {Γ} = subst (λ Γ' → Ext [] (ctx-grade Γ) Γ') (++ᶜ-identityˡ {Γ}) (ext-++ᶜ {[]} {Γ})

-- First concatenated context is also extended

ext-++ᶜ-fst : ∀ {Γ Γ' Γ'' ρ}
            → Ext (Γ' ++ᶜ Γ'') ρ Γ
            → Ext Γ' (ctx-grade Γ'' ·ᵣ ρ) Γ
        
ext-++ᶜ-fst {Γ} {Γ'} {Γ''} {ρ} id-ext rewrite ·ᵣ-identityʳ (ctx-grade Γ'')=
  ext-++ᶜ
ext-++ᶜ-fst {Γ} {Γ'} {Γ''} {ρ} (∷-ext e) =
  ∷-ext (ext-++ᶜ-fst e)
ext-++ᶜ-fst {Γ} {Γ'} {Γ''} {ρ} (⟨⟩-ext {ρ = ρ'} {ρ' = ρ''} e)
  rewrite sym (·ᵣ-assoc (ctx-grade Γ'') ρ' ρ'') =
    ⟨⟩-ext (ext-++ᶜ-fst e)

-- The extension context is bound by the sum of the extended context and ρ

grade-lt-ρ : ∀ {Γ Γ' ρ} → Ext Γ ρ Γ' → ctx-grade Γ' ≡ (ctx-grade Γ ·ᵣ ρ)
grade-lt-ρ {Γ} {Γ'} {ρ} id-ext = sym (·ᵣ-identityʳ (ctx-grade Γ))
grade-lt-ρ {Γ} {Γ'} {ρ} (∷-ext ex) = grade-lt-ρ ex
grade-lt-ρ {Γ} {Γ'' ⟨ ρ' ⟩} {ρ} (⟨⟩-ext {ρ = ρ''} ex) =
  begin
     ctx-grade (Γ'' ⟨ ρ' ⟩)
   ≡⟨⟩
     ctx-grade Γ'' ·ᵣ ρ'
   ≡⟨ cong (_·ᵣ ρ') (grade-lt-ρ ex) ⟩
     ctx-grade Γ ·ᵣ ρ'' ·ᵣ ρ'
   ≡⟨ ·ᵣ-assoc _ _ _ ⟩
     ctx-grade Γ ·ᵣ (ρ'' ·ᵣ ρ') 
   ∎

-- Composition of extensions

_∘ᵉ_ : ∀ {Γ Γ' Γ'' ρ ρ'} → Ext Γ' ρ' Γ'' → Ext Γ ρ Γ' → Ext Γ (ρ ·ᵣ ρ') Γ''
_∘ᵉ_ {ρ = ρ} id-ext e rewrite ·ᵣ-identityʳ ρ = e
_∘ᵉ_ {ρ' = ρ'} (∷-ext e') e = ∷-ext (e' ∘ᵉ e)
_∘ᵉ_ {ρ = ρ} {ρ' = .(ρ₁ ·ᵣ ρ₂)} (⟨⟩-ext {ρ = ρ₁} {ρ' = ρ₂} e') e with e' ∘ᵉ e
... | e'' rewrite (sym (·ᵣ-assoc ρ ρ₁ ρ₂)) = ⟨⟩-ext e''

-- Converting variable through extension

ext-var : ∀ {Γ Γ' A ρ ρ'}
        → Ext Γ' ρ Γ
        → A ∈[ ρ' ] Γ'
        → A ∈[ ρ' ·ᵣ ρ ] Γ
         
ext-var {Γ} {Γ'} {A} {ρ} {ρ'} id-ext x
  rewrite ·ᵣ-identityʳ ρ' = x
ext-var (∷-ext e) x =
  Tl-∷ (ext-var e x)
ext-var {Γ} {Γ'} {A} {ρ} {ρ'} (⟨⟩-ext {ρ = ρ''} {ρ' = ρ'''} e) x
  rewrite sym (·ᵣ-assoc ρ' ρ'' ρ''') = Tl-⟨⟩ (ext-var e x)

-- Variable-split contexts induce extensions

var-split-ext : {Γ Γ' Γ'' : Ctx}
              → Γ , Γ' split Γ''
              → Σ[ ρ ∈ R ] Ext Γ ρ Γ''

var-split-ext = {!!}

-- Extensions to the same context have to extend one another

ext? : {Γ Γ' Γ'' : Ctx} {ρ ρ' : R}
     → Ext Γ ρ Γ''
     → Ext Γ' ρ' Γ''
     → (Σ[ ρ'' ∈ R ] Ext Γ ρ'' Γ') ⊎ (Σ[ ρ'' ∈ R ] Ext Γ' ρ'' Γ)
     
ext? {Γ} {Γ'} {Γ''} {ρ} {ρ'} e e' = {!!}

-- Splitting a renaming by an extension (second attempt, by induction on the extended context and its variables)

split-ren : ∀ {Γ Γ' Γ'' ρ}
          → (e : Ext Γ'' ρ Γ)
          → (r : Ren Γ Γ')
          → Σ[ Γ''' ∈ Ctx ]
            Σ[ r' ∈ Ren Γ'' Γ''' ]
            Σ[ ρ' ∈ R ]
            Σ[ e' ∈ Ext Γ''' ρ' Γ' ]
            ρ' ≾ᵣ ρ ×
            (∀ {A} {ρ''} (x : A ∈[ ρ'' ] Γ'') →
              Σ[ p ∈ proj₁ (var-rename r (ext-var e x)) ≡ proj₁ (var-rename r' x) ·ᵣ ρ' ]
                subst (A ∈[_] Γ') p (proj₂ (proj₂ (var-rename r (ext-var e x)))) ≡ ext-var e' (proj₂ (proj₂ (var-rename r' x))))

split-ren {Γ} {Γ'} {[]} {ρ} e r =
  [] ,
  id-ren ,
  ctx-grade Γ' ,
  ext-[] ,
  ≾ᵣ-trans (ctx-grade-≾ r) (≾ᵣ-reflexive (trans (grade-lt-ρ e) (·ᵣ-identityˡ ρ))) ,
  λ { () }
split-ren {Γ} {Γ'} {Γ'' ∷ A} {ρ} e r with split-ren (ext-++ᶜ-fst {Γ' = Γ''} e) r
... | Γ''' , r' , ρ' , e' , rel , p with ext? e' (proj₂ (var-split-ext (proj₁ (proj₂ (proj₂ (var-split (proj₂ (proj₂ ((var-rename r) (ext-var e Hd))))))))))
... | inj₁ (ρ'' , e'') = {!!}
... | inj₂ (ρ'' , e'') =
  Γ''' ,
  ren (ctx-grade-≾ r') (λ { Hd → {!(var-rename r) (ext-var e Hd)!} ;
                            (Tl-∷ x) → var-rename r' x }) ,
  ρ' ,
  e' ,
  ≾ᵣ-trans rel (≾ᵣ-reflexive (·ᵣ-identityˡ ρ)) ,
  {!!}
split-ren {Γ} {Γ'} {Γ'' ⟨ ρ' ⟩} {ρ} e r = {!!}

{-
split-ren : ∀ {Γ Γ' Γ'' ρ}
           → Ext Γ'' ρ Γ
           → Ren Γ Γ'
           → Σ[ Γ''' ∈ Ctx ] (Ren Γ'' Γ''' × Σ[ ρ' ∈ R ] ρ' ≾ᵣ ρ × Ext Γ''' ρ' Γ')

split-ren {Γ} {Γ'} {[]} {ρ} e r rewrite sym (trans (grade-lt-ρ e) (·ᵣ-identityˡ ρ)) =
  [] , id-ren , ctx-grade Γ' , ctx-grade-≾ r , ext-[]
split-ren {Γ} {Γ'} {Γ'' ∷ B} {ρ} e r with split-ren (ext-++ᶜ-fst {Γ' = Γ''} e) r
... | Γ''' , r' , ρ' , rel , e' with ext? e' (proj₂ (var-split-ext (proj₁ (proj₂ (proj₂ (var-split (proj₂ (proj₂ ((var-rename r) (ext-var e Hd))))))))))
... | inj₁ (ρ'' , e'') =
  proj₁ (var-split (proj₂ (proj₂ ((var-rename r) (ext-var e Hd))))) ∷ B ,
  {!!} ,
  {!!} ,
  {!!} ,
  proj₂ (var-split-ext (proj₁ (proj₂ (proj₂ (var-split (proj₂ (proj₂ ((var-rename r) (ext-var e Hd)))))))))
... | inj₂ (ρ'' , e'') = {!!}
split-ren {Γ} {Γ'} {Γ'' ⟨ ρ' ⟩} {ρ} e r = {!!}
-}

-- Concatenation of extensions

++ᶜ-ext : ∀ {Γ Γ' Γ'' ρ} → Ext Γ ρ Γ' → Ext (Γ'' ++ᶜ Γ) ρ (Γ'' ++ᶜ Γ')
++ᶜ-ext id-ext     = id-ext
++ᶜ-ext (∷-ext e)  = ∷-ext (++ᶜ-ext e)
++ᶜ-ext (⟨⟩-ext e) = ⟨⟩-ext (++ᶜ-ext e)

-- If Γ is extended by Γ' but Γ is "bigger" than Γ', then we reach a contradiction

id-ext-split-≢-contradiction-∷ : ∀ {Γ Γ' A B ρ₁ ρ₂}
                               → (x : A ∈[ ρ₁ ] Γ')
                               → (y : A ∈[ ρ₂ ] Γ)
                               → proj₁ (var-split y) ≡ proj₁ (var-split x)
                               → proj₁ (proj₂ (var-split y)) ≡ proj₁ (proj₂ (var-split x)) ∷ B
                               → Ext Γ uᵣ Γ'
                               → ⊥
                               
id-ext-split-≢-contradiction-∷ {Γ} {Γ'} x y eq₁ eq₂ e rewrite (sym (split-struct-≡ x y eq₁ eq₂)) =
  ext-decrease-contradiction (λ { () }) e

id-ext-split-≢-contradiction-⟨⟩ : ∀ {Γ Γ' A ρ' ρ₁ ρ₂}
                            → (x : A ∈[ ρ₁ ] Γ')
                            → (y : A ∈[ ρ₂ ] Γ)
                            → proj₁ (var-split y) ≡ proj₁ (var-split x)
                            → proj₁ (proj₂ (var-split y)) ≡ proj₁ (proj₂ (var-split x)) ⟨ ρ' ⟩
                            → Ext Γ uᵣ Γ'
                            → ⊥
                            
id-ext-split-≢-contradiction-⟨⟩ {Γ' = Γ'} x y eq₁ eq₂ e rewrite (sym (split-struct-≡ x y eq₁ eq₂)) =
 ext-decrease-contradiction (λ {()}) e









{-
{-
left-split-ren : ∀ {Γ Γ' Γ''} → Ren (Γ ++ᶜ Γ') Γ'' → Σ[ Γ₁ ∈ Ctx ] (Σ[ Γ₂ ∈ Ctx ] (Ren Γ Γ₁ × (Γ₁ , Γ₂ split Γ'') ))
left-split-ren {Γ'' = []} r = [] , [] , {!!} , split-[]
left-split-ren {Γ} {Γ'} {Γ'' ∷ A} r with left-split-ren {Γ} {Γ'} {Γ''} {!!}
... | Γ₁ , Γ₂ , r' , s = Γ₁ , Γ₂ ∷ A , r' , split-∷ s
left-split-ren {Γ} {Γ'} {Γ'' ⟨ ρ ⟩} r
  with left-split-ren {Γ} {Γ'} {Γ''} (ren (≾ᵣ-trans (c≾ᵣc·ᵣd {d = ρ}) (ctx-grade-≾ r)) {!!})
... | Γ₁ , Γ₂ , r' , s = Γ₁ , Γ₂ ⟨ ρ ⟩ , r' , split-⟨⟩ s
-}

{-
left-split-ren : ∀ {Γ Γ' Γ''} → Ren (Γ ++ᶜ Γ') Γ'' → Σ[ Γ₁ ∈ Ctx ] (Σ[ Γ₂ ∈ Ctx ] (Ren Γ Γ₁ × Γ'' ≡ Γ₁  ++ᶜ Γ₂ ))
left-split-ren {Γ} {[]} {Γ''} r =
Γ'' , [] , r , refl
left-split-ren {Γ} {Γ' ∷ A} {Γ''} r = {!!}
left-split-ren {Γ} {Γ' ⟨ ρ ⟩} {Γ''} r = {!!}
-}

-- Converting variable through extension

ext-var : ∀ {Γ Γ' A ρ ρ'}
        → Ext Γ' ρ Γ
        → A ∈[ ρ' ] Γ'
        → Σ[ ρ'' ∈ R ] A ∈[ ρ'' ] Γ
        
ext-var id-ext x = _ , x
ext-var (∷-ext e) x with ext-var e x
... | ρ'' , y = _ , Tl-∷ y
ext-var (⟨⟩-ext {ρ' = ρ'} e) x with ext-var e x
... | ρ'' , y = _ , Tl-⟨⟩ y

--

ext-remove-one : ∀ {Γ Γ' A ρ ρ'}
               → Ext (Γ ∷ A) ρ Γ'
               → (x : A ∈[ ρ' ] Γ')
               → Ext Γ ρ (proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)))
               × Ren (proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x))) Γ'
ext-remove-one e x = {!!}

--
wk-ctx-ext : ∀ {Γ Γ' A ρ ρ'} → Ext Γ ρ Γ' → A ∈[ ρ' ] Γ' → Ext (Γ ∷ A) ρ Γ'
wk-ctx-ext e x = {!!}

-- Adding part of the grade difference to the extended contexts
-- keeps the extension, changing the grade difference

ext-shift-grade : ∀ {Γ Γ' ρ ρ' ρ''}
                → Ext Γ (uᵣ ·ᵣ ρ) (Γ ⟨ ρ ⟩)
                → Ext Γ ρ' Γ'
                → ρ' ≾ᵣ (ρ ·ᵣ ρ'')
                → Ext (Γ ⟨ ρ ⟩) ρ'' Γ'
ext-shift-grade {Γ} {Γ'} e₁ e₂ rel = {!!}

-- Splitting a renaming by an extension (second attempt, by induction on the extended context and its variables)
split-ren : ∀ {Γ Γ' Γ'' ρ}
           → Ext Γ'' ρ Γ
           → Ren Γ Γ'
           → Σ[ Γ''' ∈ Ctx ] (Ren Γ'' Γ''' × Σ[ ρ' ∈ R ] ρ' ≾ᵣ ρ × Ext Γ''' ρ' Γ')

split-ren {Γ} {Γ'} {[]} {ρ} e r rewrite sym (trans (grade-lt-ρ e) (·ᵣ-identityˡ ρ)) =
  [] , id-ren , ctx-grade Γ' , ctx-grade-≾ r , ext-[]
split-ren {Γ} {Γ'} {Γ'' ∷ A} {ρ} e r with ext-remove-one e (proj₂ (ext-var e (Hd {Γ = Γ''})))
... | e' , r' with split-ren e' (r ∘ʳ r')
... | Γ'''' , r'' , ρ' , rel , e'' = Γ'''' ∷ A , cong-∷-ren r'' , ρ' , rel , {!!}
split-ren {Γ} {Γ'} {Γ'' ⟨ ρ'' ⟩} {ρ} e r with split-ren (ext-++ᶜ-fst {Γ' = Γ''} e) r
... | Γ''' , r' , ρ' , rel , e' =
  Γ''' ⟨ ρ'' ⟩ ,
  cong-⟨⟩-ren r' ,
  ρ ,
  ≾ᵣ-refl ,
  ext-shift-grade (⟨⟩-ext id-ext) e' (≾ᵣ-trans rel (·ᵣ-monoˡ-≾ᵣ (≾ᵣ-reflexive (·ᵣ-identityˡ ρ''))))

-}

{-
split-ren : ∀ {Γ Γ' Γ'' ρ}
           → Ext Γ'' ρ Γ
           → Ren Γ Γ'
           → Σ[ Γ''' ∈ Ctx ] (Ren Γ'' Γ''' × Σ[ ρ' ∈ R ] ρ' ≾ᵣ ρ × Ext Γ''' ρ' Γ')

split-ren {Γ} {Γ'} {[]} {ρ} e r rewrite sym (trans (grade-lt-ρ e) (·ᵣ-identityˡ ρ)) =
  [] , id-ren , ctx-grade Γ' , ctx-grade-≾ r , ext-[]
split-ren {Γ} {Γ'} {Γ'' ∷ A} {ρ} e r with split-ren (ext-++ᶜ-fst {Γ' = Γ''} e) r
... | Γ''' , r' , ρ' , rel , e' =
  Γ''' ∷ A ,
  cong-∷-ren r' ,
  ρ' ,
  ≾ᵣ-trans rel (≾ᵣ-reflexive (·ᵣ-identityˡ ρ)) ,
  wk-ctx-ext e' (proj₂ (proj₂ (var-rename r (proj₂ (ext-var e Hd)))))
split-ren {Γ} {Γ'} {Γ'' ⟨ ρ'' ⟩} {ρ} e r with split-ren (ext-++ᶜ-fst {Γ' = Γ''} e) r
... | Γ''' , r' , ρ' , rel , e' =
  Γ''' ⟨ ρ'' ⟩ ,
  cong-⟨⟩-ren r' ,
  ρ ,
  ≾ᵣ-refl ,
  ext-shift-grade (⟨⟩-ext id-ext) e' (≾ᵣ-trans rel (·ᵣ-monoˡ-≾ᵣ (≾ᵣ-reflexive (·ᵣ-identityˡ ρ''))))
-}
