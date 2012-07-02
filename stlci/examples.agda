module stlci.examples where

open import Data.Empty
open import Relation.Binary.PropositionalEquality

open import tools.contexts
open import stlci.definition
open import stlci.model
open import stlci.eval

{- Because of the existence of normal forms, one can prove
   that the calculus is consistent. This is the analogous of
   the cut-elimination procedure. -}

ε⊢ne-empty : ∀ {A} (t : ε ⊢ne A) → ⊥
ε⊢ne-empty (:v ())
ε⊢ne-empty (:a t u) = ε⊢ne-empty t
ε⊢ne-empty (p[] m t) = ε⊢ne-empty m
ε⊢ne-empty (p+ m t₁ t₂) = ε⊢ne-empty m
ε⊢ne-empty (p× m t) = ε⊢ne-empty m
ε⊢ne-empty (pμ m t) = ε⊢ne-empty m
ε⊢ne-empty (μμ m t) = ε⊢ne-empty m

no-empty-nf : (t : ε ⊢nf μ []) → ⊥
no-empty-nf (⇈μ ne) = ε⊢ne-empty ne
no-empty-nf (:C (:r t)) = no-empty-nf t

consistency : (t : ε ⊢ μ []) → ⊥
consistency t = no-empty-nf (to-the-future t)

{- mapping swap twice on a structure is the same as
   mapping the identity on it! -}

swap : ∀ {Γ d₁ d₂ σ} → Γ ⊢ F[ d₁ × d₂ ] σ ▹ F[ d₂ × d₁ ] σ
swap = :λ (p× (:v here!) (:λ (:λ (:× (:v here!) (:v (there here!))))))

swap²-simpl : ∀ {Γ d₁ d₂ σ} → norm (swap :∘ swap) ≡ norm (id {Γ} {F[ d₁ × d₂ ] σ})
swap²-simpl = {!!}