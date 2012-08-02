module stlcl.simple.examples where

open import Relation.Binary.PropositionalEquality

open import tools.contexts
open import stlcl.definition
open import stlcl.reductions
open import stlcl.simple.eval

id : ∀ {Γ σ} → Γ ⊢ σ `→ σ
id = `λ (`v here!)

swap : ∀ {Γ σ τ} → Γ ⊢ σ `× τ `→ τ `× σ
swap = `λ (`π₂ (`v here!) `, `π₁ (`v here!))

map-swap² : ∀ {Γ σ τ} (xs : Γ ⊢ `list (σ `× τ)) →
  norm (`map (swap `∘ swap) xs) ≡ norm (`map id xs)
map-swap² xs = refl