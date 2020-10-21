{-# OPTIONS --safe #-}

module Quotable where

open import Level using (Level)
open import Data.Nat using (ℕ)
open import Data.Word using (Word64)
open import Data.String using (String)
open import Data.Char using (Char)
open import Data.Float using (Float)

open import Reflection
open import Reflection.Argument.Visibility
open import Reflection.Argument.Relevance
open import Reflection.Argument.Information

open import ReflectionHelpers

private
  variable
    ℓ : Level
    A : Set ℓ

record Quotable (A : Set ℓ) : Set ℓ where
  field quoteVal : A → Term

open Quotable ⦃ ... ⦄ public

instance
  qℕ : Quotable ℕ
  qℕ .quoteVal n = lit (nat n)

  qWord : Quotable Word64
  qWord .quoteVal w = lit (word64 w)

  qChar : Quotable Char
  qChar .quoteVal s = lit (char s)

  qString : Quotable String
  qString .quoteVal s = lit (string s)

  qFloat : Quotable Float
  qFloat .quoteVal s = lit (float s)

  qName : Quotable Name
  qName .quoteVal x = lit (name x)

  qMeta : Quotable Meta
  qMeta .quoteVal x = lit (meta x)

  qVis : Quotable Visibility
  qVis .quoteVal visible   = con₀ (quote visible)
  qVis .quoteVal hidden    = con₀ (quote hidden)
  qVis .quoteVal instance′ = con₀ (quote instance′)

  qRel : Quotable Relevance
  qRel .quoteVal relevant   = con₀ (quote relevant)
  qRel .quoteVal irrelevant = con₀ (quote irrelevant)

  qInfo : Quotable ArgInfo
  qInfo .quoteVal (arg-info v r) = con₂ (quote arg-info) (quoteVal v) (quoteVal r)

  qLit : Quotable Literal
  qLit .quoteVal (nat n)    = con₁ (quote nat)          (quoteVal n)
  qLit .quoteVal (word64 n) = con₁ (quote word64)       (quoteVal n)
  qLit .quoteVal (string n) = con₁ (quote string)       (quoteVal n)
  qLit .quoteVal (char n)   = con₁ (quote char)         (quoteVal n)
  qLit .quoteVal (float n)  = con₁ (quote float)        (quoteVal n)
  qLit .quoteVal (name n)   = con₁ (quote name)         (quoteVal n)
  qLit .quoteVal (meta n)   = con₁ (quote Literal.meta) (quoteVal n)
