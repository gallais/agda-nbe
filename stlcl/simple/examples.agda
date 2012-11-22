module stlclb.simple.examples where

open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import tools.contexts
open import stlclb.definition
open import stlclb.reductions
open import stlclb.simple.eval

postulate
  n : ℕ

id : ∀ {Γ} {σ : ty n} → Γ ⊢ σ `→ σ
id = `λ (`v here!)

swap : ∀ {Γ} {σ τ : ty n} → Γ ⊢ σ `× τ `→ τ `× σ
swap = `λ (`π₂ (`v here!) `, `π₁ (`v here!))

map-swap² : ∀ {Γ} {σ τ : ty n} (xs : Γ ⊢ `list (σ `× τ)) →
  norm (`map (swap `∘ swap) xs) ≡ norm (`map id xs)
map-swap² xs = refl