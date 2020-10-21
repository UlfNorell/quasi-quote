{-# OPTIONS --safe #-}

module ReflectionHelpers where

open import Level using (Level)
open import Data.Bool
open import Data.List
open import Data.Nat
open import Data.Maybe
import Data.Maybe.Categorical as Maybe using (applicative)
open import Category.Monad
open import Reflection
open import Reflection.TypeChecking.Monad.Categorical
import Reflection.Traversal as Traverse

private
  variable
    ℓ : Level
    A : Set ℓ

------------------------------------------------------------------------
-- Strengthening

module _ where

  open Traverse Maybe.applicative

  private
    strVar : ℕ → Cxt → ℕ → Maybe ℕ
    strVar by (from , Γ) i with i <ᵇ from | i <ᵇ from + by
    ... | true | _    = just i
    ... | _    | true = nothing
    ... | _    | _    = just (i ∸ by)

    actions : ℕ → Actions
    actions by = record defaultActions { onVar = strVar by }

  strengthenFromBy′ : (Actions → Cxt → A → Maybe A) → (from by : ℕ) → A → Maybe A
  strengthenFromBy′ trav from by = trav (actions by) (from , []) -- not using the context part

  strengthenFromBy : (from by : ℕ) → Term → Maybe Term
  strengthenFromBy = strengthenFromBy′ traverseTerm

  strengthenBy : ℕ → Term → Maybe Term
  strengthenBy = strengthenFromBy 0

con₀ : Name → Term
con₀ f = con f []

con₁ : Name → Term → Term
con₁ f a = con f (vArg a ∷ [])

con₂ : Name → Term → Term → Term
con₂ f a b = con f (vArg a ∷ vArg b ∷ [])

con₃ : Name → Term → Term → Term → Term
con₃ f a b c = con f (vArg a ∷ vArg b ∷ vArg c ∷ [])

def₁ : Name → Term → Term
def₁ f a = def f (vArg a ∷ [])

def₂ : Name → Term → Term → Term
def₂ f a b = def f (vArg a ∷ vArg b ∷ [])
