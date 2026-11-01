------------------------------------------------------------------------
-- Named variables for the inference examples                         --
--                                                                    --
-- De Bruijn indices from zero, with display forms so that Agda shows --
-- them by these names. The module takes no parameters, as display    --
-- forms require.                                                     --
--                                                                    --
-- Where to look                                                      --
--   α₀ α₁ …   type variables                                         --
--   ρ₀ ρ₁ …   resource-grade variables                               --
--   ε₀ ε₁ …   effect-grade variables                                 --
--   v₀ v₁ …   raw term variables                                     --
------------------------------------------------------------------------

import Data.Fin as Fin
open import Data.Nat using (_+_)

open import Language.Spec using (LanguageSpec)

open import PolymorphicCalculus.Syntax.Scopes using (scope)

import PolymorphicCalculus.Syntax.Grades as G
import PolymorphicCalculus.Syntax.Types  as T
import PolymorphicCalculus.Syntax.Raw    as Raw

module PolymorphicCalculus.Examples.Variables where

-- Type variables

α₀ : ∀ {S : LanguageSpec} {n r e} → T.OVType S (scope (1 + n) r e)
α₀ = T.tvar Fin.zero

α₁ : ∀ {S : LanguageSpec} {n r e} → T.OVType S (scope (2 + n) r e)
α₁ = T.tvar (Fin.suc Fin.zero)

α₂ : ∀ {S : LanguageSpec} {n r e} → T.OVType S (scope (3 + n) r e)
α₂ = T.tvar (Fin.suc (Fin.suc Fin.zero))

α₃ : ∀ {S : LanguageSpec} {n r e} → T.OVType S (scope (4 + n) r e)
α₃ = T.tvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))

α₄ : ∀ {S : LanguageSpec} {n r e} → T.OVType S (scope (5 + n) r e)
α₄ = T.tvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))

α₅ : ∀ {S : LanguageSpec} {n r e} → T.OVType S (scope (6 + n) r e)
α₅ = T.tvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))

{-# DISPLAY T.tvar Fin.zero = α₀ #-}
{-# DISPLAY T.tvar (Fin.suc Fin.zero) = α₁ #-}
{-# DISPLAY T.tvar (Fin.suc (Fin.suc Fin.zero)) = α₂ #-}
{-# DISPLAY T.tvar (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = α₃ #-}
{-# DISPLAY T.tvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = α₄ #-}
{-# DISPLAY T.tvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) = α₅ #-}

-- Resource-grade variables

ρ₀ : ∀ {S : LanguageSpec} {n r e} → G.RExp S (scope n (1 + r) e)
ρ₀ = G.rvar Fin.zero

ρ₁ : ∀ {S : LanguageSpec} {n r e} → G.RExp S (scope n (2 + r) e)
ρ₁ = G.rvar (Fin.suc Fin.zero)

ρ₂ : ∀ {S : LanguageSpec} {n r e} → G.RExp S (scope n (3 + r) e)
ρ₂ = G.rvar (Fin.suc (Fin.suc Fin.zero))

ρ₃ : ∀ {S : LanguageSpec} {n r e} → G.RExp S (scope n (4 + r) e)
ρ₃ = G.rvar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))

ρ₄ : ∀ {S : LanguageSpec} {n r e} → G.RExp S (scope n (5 + r) e)
ρ₄ = G.rvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))

ρ₅ : ∀ {S : LanguageSpec} {n r e} → G.RExp S (scope n (6 + r) e)
ρ₅ = G.rvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))

{-# DISPLAY G.rvar Fin.zero = ρ₀ #-}
{-# DISPLAY G.rvar (Fin.suc Fin.zero) = ρ₁ #-}
{-# DISPLAY G.rvar (Fin.suc (Fin.suc Fin.zero)) = ρ₂ #-}
{-# DISPLAY G.rvar (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = ρ₃ #-}
{-# DISPLAY G.rvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = ρ₄ #-}
{-# DISPLAY G.rvar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) = ρ₅ #-}

-- Effect-grade variables

ε₀ : ∀ {S : LanguageSpec} {n r e} → G.EExp S (scope n r (1 + e))
ε₀ = G.evar Fin.zero

ε₁ : ∀ {S : LanguageSpec} {n r e} → G.EExp S (scope n r (2 + e))
ε₁ = G.evar (Fin.suc Fin.zero)

ε₂ : ∀ {S : LanguageSpec} {n r e} → G.EExp S (scope n r (3 + e))
ε₂ = G.evar (Fin.suc (Fin.suc Fin.zero))

ε₃ : ∀ {S : LanguageSpec} {n r e} → G.EExp S (scope n r (4 + e))
ε₃ = G.evar (Fin.suc (Fin.suc (Fin.suc Fin.zero)))

ε₄ : ∀ {S : LanguageSpec} {n r e} → G.EExp S (scope n r (5 + e))
ε₄ = G.evar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))

ε₅ : ∀ {S : LanguageSpec} {n r e} → G.EExp S (scope n r (6 + e))
ε₅ = G.evar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))

{-# DISPLAY G.evar Fin.zero = ε₀ #-}
{-# DISPLAY G.evar (Fin.suc Fin.zero) = ε₁ #-}
{-# DISPLAY G.evar (Fin.suc (Fin.suc Fin.zero)) = ε₂ #-}
{-# DISPLAY G.evar (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = ε₃ #-}
{-# DISPLAY G.evar (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = ε₄ #-}
{-# DISPLAY G.evar (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) = ε₅ #-}

-- Raw term variables

v₀ : ∀ {S : LanguageSpec} {Θ n} → Raw.RawV S Θ (1 + n)
v₀ = Raw.var Fin.zero

v₁ : ∀ {S : LanguageSpec} {Θ n} → Raw.RawV S Θ (2 + n)
v₁ = Raw.var (Fin.suc Fin.zero)

v₂ : ∀ {S : LanguageSpec} {Θ n} → Raw.RawV S Θ (3 + n)
v₂ = Raw.var (Fin.suc (Fin.suc Fin.zero))

v₃ : ∀ {S : LanguageSpec} {Θ n} → Raw.RawV S Θ (4 + n)
v₃ = Raw.var (Fin.suc (Fin.suc (Fin.suc Fin.zero)))

v₄ : ∀ {S : LanguageSpec} {Θ n} → Raw.RawV S Θ (5 + n)
v₄ = Raw.var (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))

v₅ : ∀ {S : LanguageSpec} {Θ n} → Raw.RawV S Θ (6 + n)
v₅ = Raw.var (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))

{-# DISPLAY Raw.var Fin.zero = v₀ #-}
{-# DISPLAY Raw.var (Fin.suc Fin.zero) = v₁ #-}
{-# DISPLAY Raw.var (Fin.suc (Fin.suc Fin.zero)) = v₂ #-}
{-# DISPLAY Raw.var (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = v₃ #-}
{-# DISPLAY Raw.var (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = v₄ #-}
{-# DISPLAY Raw.var (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) = v₅ #-}
