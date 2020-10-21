{-# OPTIONS --safe #-}

module Examples where

open import Level using (Level)
open import Data.List
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.String
open import Relation.Binary.PropositionalEquality
open import Category.Monad
open import Function

open import Reflection hiding (_>>=_; _>>_) renaming (agda-sort to sort)
open import Reflection.TypeChecking.Monad.Categorical using (monad)
open import Reflection.Universe

open Pattern
open Sort
open Clause

open import Quotable
open import QuasiQuoting
open import ReflectionHelpers

open import Agda.Builtin.Reflection using (onlyReduceDefs)

private
  open module MonadTC {ℓ} = RawMonad {ℓ} monad renaming (_⊛_ to _<*>_)

private
  variable
    ℓ : Level
    A B : Set ℓ
    u : Univ

-- Example: simple

test₁ : Term → Term
test₁ t = ` λ n → n + ! t

check₁ : test₁ (var 0 []) ≡ lam visible (abs "n" (def₂ (quote _+_) (var 0 []) (var 1 [])))
check₁ = refl                                          -- Lifted automatically ^^^^^^^^

-- Example: building terms with quasi-quoting

test : Term → Term
test B = ` ((A : Set) (x : !⟨ B ∶ Set ⟩) → !⟨ B ∶ Set ⟩)

pattern [_∶_]→_ x a b = pi (vArg a) (abs x b)
infixr 5 [_∶_]→_

check : test (var 0 []) ≡ [ "A" ∶ sort (lit 0) ]→
                          [ "x" ∶ var 1 []     ]→
                          var 2 []
check = refl

foo : ℕ → Term
foo n = ` λ x → x + n

nAry : ℕ → Term → Term → Term
nAry zero    A B = B
nAry (suc n) A B = ` (!⟨ A ∶ Set ⟩ → !⟨ nAry n A B ∶ Set ⟩)

-- Example: nested quotes

plus1 : Term → Term
plus1 t = ` ! t + 1

nested : Term → Term
nested t = ` ! plus1 (` 2 * ! t) + 5

check-nested : ∀ t → nested t ≡ (` 2 * ! t + 1 + 5)
check-nested t = refl

-- Example: trying to break things

-- bad : Term
-- bad = ` λ t → !⟨ t ∶ Term ⟩   -- Phase violation: quoted variable used in splice

-- boom : ⊥
-- boom = ! lit (nat 4) -- Phase violation: splice used outside quote

-- escape : Term
-- escape = `_ λ {i} → i   -- Phase violation: InsideQoute token escaping the quote

-- Example: Quotable instance for lists

instance
  qList : ⦃ Quotable A ⦄ → Quotable (List A)
  qList {A = A} .quoteVal []       = `⟨ [] ∶ List A ⟩
  qList {A = A} .quoteVal (x ∷ xs) = ` x ∷ xs



-- Example: function application on reflected syntax
-- Awkward since β-redexes are not representable in the reflected syntax.

-- Hard to get this to work with the unsolved metas!

private
  app : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
  app f = f

tcApply : Term → Term → TC Term
tcApply f x = onlyReduceDefs (quote app ∷ []) (reduce (def (quote app) (vArg f ∷ vArg x ∷ [])))
-- tcApply f x = onlyReduceDefs (quote app ∷ []) (reduce (def₂ (quote app) f x))
-- ^^ this doesn't work because onlyReduceDefs kicks in and refuses to reduce def₂

macro
  testApply : (A → B) → A → Term → TC ⊤
  testApply f x hole = do
    `f  ← quoteTC f
    `x  ← quoteTC x
    `fx ← tcApply `f `x
    unify hole =<< quoteTC `fx

_ : testApply (λ n → n + 1) 5 ≡ def (quote _+_) (vArg (lit (nat 5)) ∷ vArg (lit (nat 1)) ∷ [])
_ = refl

-- Example: Quotable instances for reflected syntax

qRefl : ⟦ u ⟧ → Term
qRefl {⟨term⟩}    (var x args)           = ` Term.var x (! qRefl args)
qRefl {⟨term⟩}    (con c args)           = ` Term.con c (! qRefl args)
qRefl {⟨term⟩}    (def f args)           = ` def f (! qRefl args)
qRefl {⟨term⟩}    (lam v t)              = ` lam v (! qRefl t)
qRefl {⟨term⟩}    (pat-lam cs args)      = ` pat-lam (! qRefl cs) (! qRefl args)
qRefl {⟨term⟩}    (pi a b)               = ` pi (! qRefl a) (! qRefl b)
qRefl {⟨term⟩}    (sort s)               = ` sort (! qRefl s)
qRefl {⟨term⟩}    (lit l)                = ` Term.lit l
qRefl {⟨term⟩}    (meta x args)          = ` Term.meta x (! qRefl args)
qRefl {⟨term⟩}    unknown                = ` Term.unknown
qRefl {⟨pat⟩}     (con c ps)             = ` Pattern.con c (! qRefl ps)
qRefl {⟨pat⟩}     (dot t)                = ` dot (! qRefl t)
qRefl {⟨pat⟩}     (var x)                = ` Pattern.var x
qRefl {⟨pat⟩}     (lit l)                = ` Pattern.lit l
qRefl {⟨pat⟩}     (proj f)               = ` proj f
qRefl {⟨pat⟩}     absurd                 = ` absurd
qRefl {⟨sort⟩}    (set t)                = ` set (! qRefl t)
qRefl {⟨sort⟩}    (lit n)                = ` Sort.lit n
qRefl {⟨sort⟩}    unknown                = ` Sort.unknown
qRefl {⟨clause⟩}  (clause tel ps t)      = ` clause (! qRefl tel) (! qRefl ps) (! qRefl t)
qRefl {⟨clause⟩}  (absurd-clause tel ps) = ` absurd-clause (! qRefl tel) (! qRefl ps)
qRefl {⟨list⟩ u}  []                     = `⟨ [] ∶ List ⟦ u ⟧ ⟩
qRefl {⟨list⟩ u}  (x ∷ xs)               = `⟨ ! qRefl x ∷ ! qRefl xs ∶ List ⟦ u ⟧ ⟩
qRefl {⟨arg⟩ u}   (arg i x)              = `⟨ arg i (! qRefl x) ∶ Arg ⟦ u ⟧ ⟩
qRefl {⟨abs⟩ u}   (abs s x)              = `⟨ abs s (! qRefl x) ∶ Abs ⟦ u ⟧ ⟩
qRefl {⟨named⟩ u} (x , t)                = `⟨ x , (! qRefl t) ∶ String × ⟦ u ⟧ ⟩

instance
  qTerm : Quotable Term
  qTerm .quoteVal = qRefl

  -- ...
