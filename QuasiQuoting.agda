{-# OPTIONS --safe #-}

module QuasiQuoting where

open import Level using (Level)
open import Data.Unit using (⊤)
open import Data.Bool
open import Data.Nat
open import Data.List
open import Data.Empty using (⊥)
open import Data.Maybe hiding (_>>=_; map)
open import Data.Word using (Word64)
open import Data.String using (String)
open import Data.Char using (Char)
open import Data.Float using (Float)
open import Data.Product using (_×_; _,_)
open import Category.Monad using (RawMonad)
open import Function
open import Relation.Binary.PropositionalEquality

open import Reflection hiding (_>>=_; _>>_; return) renaming (agda-sort to sort)
open import Reflection.Universe
open import Reflection.DeBruijn
open import Reflection.TypeChecking.Monad.Categorical using (monad)
open import Reflection.Argument.Visibility
open import Reflection.Argument.Relevance
open import Reflection.Argument.Information
import Reflection.Traversal as Traverse
open import Agda.Builtin.Reflection using (onlyReduceDefs) renaming (primMetaLess to _<ᵐ_)

open import Quotable
open import ReflectionHelpers

private
  variable
    ℓ   : Level
    A B : Set ℓ
    u   : Univ

private
  open module MonadTC {ℓ} = RawMonad {ℓ} monad renaming (_⊛_ to _<*>_)

open Pattern
open Sort
open Clause

pattern ⟨tel⟩ = ⟨list⟩ (⟨named⟩ (⟨arg⟩ ⟨term⟩))

data InsideQuote : Set where

ensureInsideQuote : Term → TC ⊤
ensureInsideQuote hole = do
  n ← length <$> getContext
  foldr catchTC (typeErrorFmt "Phase violation: splice used outside quote")
    (map (λ i → unify hole (var i [])) (downFrom n))

-- The (empty) InsideQuote argument guarantees that splice can only be
-- used inside a quote. Use a tactic argument instead of an instance
-- argument to make it possible to nest quotes.
!_ : {@(tactic ensureInsideQuote) i : InsideQuote} → Term → A
!_ {i = ()}

!⟨_∶_⟩ : {@(tactic ensureInsideQuote) _ : InsideQuote} → Term → (A : Set ℓ) → A
!⟨ t ∶ _ ⟩ = ! t

splice : ℕ → Term → TC Term
splice 0 `t = pure `t
splice n `t = do
  just `t ← pure $ strengthenBy n `t
    where nothing → typeErrorFmt "Phase violation: quoted variable used in splice"
  return (def₂ (quote weaken) (lit (nat n)) `t)

qquote : ℕ → ⟦ u ⟧ → TC Term
qquote {⟨term⟩} n (def (quote !_)     (hArg _ ∷ hArg _ ∷ hArg _ ∷ vArg `t ∷ [])) = splice n `t
qquote {⟨term⟩} n (def (quote !⟨_∶_⟩) (hArg _ ∷ hArg _ ∷ vArg `t ∷ vArg _ ∷ [])) = splice n `t
qquote {⟨term⟩} n t@(var x args) =
  if x <ᵇ n then con₂ (quote Term.var) (quoteVal x) <$> qquote n args
            else splice n (def₁ (quote quoteVal) t)
qquote {⟨term⟩}    n (con c args)           = con₂ (quote Term.con) (quoteVal c) <$> qquote n args
qquote {⟨term⟩}    n (def f args)           = con₂ (quote def) (quoteVal f) <$> qquote n args
qquote {⟨term⟩}    n (lam v b)              = con₂ (quote lam) (quoteVal v) <$> qquote n b
qquote {⟨term⟩}    n (pat-lam cs args)      = con₂ (quote pat-lam) <$> qquote n cs <*> qquote n args
qquote {⟨term⟩}    n (pi a b)               = con₂ (quote pi) <$> qquote n a <*> qquote n b
qquote {⟨term⟩}    n (sort s)               = con₁ (quote sort) <$> qquote n s
qquote {⟨term⟩}    n (lit l)                = pure $ con₁ (quote Term.lit) (quoteVal l)
qquote {⟨term⟩}    n t@(meta x args)        = blockOnMeta x
qquote {⟨term⟩}    n unknown                = pure $ con (quote Term.unknown) []
qquote {⟨pat⟩}     n (con c ps)             = con₂ (quote Pattern.con) (quoteVal c) <$> qquote n ps
qquote {⟨pat⟩}     n (dot t)                = con₁ (quote dot) <$> qquote n t
qquote {⟨pat⟩}     n (var x)                = pure $ con₁ (quote Pattern.var) (quoteVal x)
qquote {⟨pat⟩}     n (lit l)                = pure $ con₁ (quote Pattern.lit) (quoteVal l)
qquote {⟨pat⟩}     n (proj f)               = pure $ con₁ (quote proj) (quoteVal f)
qquote {⟨pat⟩}     n absurd                 = pure $ con (quote absurd) []
qquote {⟨sort⟩}    n (set t)                = con₁ (quote Sort.set) <$> qquote n t
qquote {⟨sort⟩}    n (lit l)                = pure $ con₁ (quote Sort.lit) (quoteVal l)
qquote {⟨sort⟩}    n unknown                = pure $ con (quote Sort.unknown) []
qquote {⟨clause⟩}  n (clause tel ps t)      = con₃ (quote clause) <$> qquote n tel <*> qquote n′ ps <*> qquote n′ t
  where n′ = n + length tel
qquote {⟨clause⟩}  n (absurd-clause tel ps) = con₂ (quote absurd-clause) <$> qquote n tel <*> qquote n′ ps
  where n′ = n + length tel
qquote {⟨list⟩ u}  n []                     = pure (con (quote List.[]) [])
qquote {⟨tel⟩}     n (dom ∷ Γ)              = con₂ (quote List._∷_) <$> qquote n dom <*> qquote (suc n) Γ
qquote {⟨list⟩ u}  n (x ∷ xs)               = con₂ (quote List._∷_) <$> qquote n x <*> qquote n xs
qquote {⟨arg⟩ u}   n (arg i x)              = con₂ (quote arg) (quoteVal i) <$> qquote n x
qquote {⟨abs⟩ u}   n (abs x t)              = con₂ (quote abs) (quoteVal x) <$> qquote (suc n) t
qquote {⟨named⟩ u} n (x , t)                = con₂ (quote _,_) (quoteVal x) <$> qquote n t

blockIfMeta : Term → TC Term
blockIfMeta (meta x _) = blockOnMeta x
blockIfMeta t = pure t

quasiQuote : ({InsideQuote} → A) → Term → TC ⊤
quasiQuote x hole = do
  lam _ (abs _ t) ← quoteTC (λ i → x {i})
    where t → typeErrorFmt "Impossible: %t" t
  just t ← strengthen <$> qquote 0 t
    where nothing → typeErrorFmt "Phase violation: InsideQuote token escaping the quote"
  unify hole t

macro
  typedQuasiQuote = quasiQuote
  syntax typedQuasiQuote {A = A} x = `⟨ x ∶ A ⟩

  infix 0 `_
  `_ = quasiQuote
