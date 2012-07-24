module stlc.eval where

open import Data.Unit
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

open import tools.contexts
open import tools.closures
open import stlc.definition
open import stlc.reductions
open import stlc.model

{- definition of the trivial environment -}

⊩τvar : {Γ : Con ty} (σ : ty) → (Γ ∙ σ) ⊩τ σ [ var here! ]
⊩τvar σ = ↓ {σ} (var here!)

Γ⊩ε_ : (Γ : Con ty) → Γ ⊩ε Γ [ Γ⊩ Γ ]
Γ⊩ε ε = tt
Γ⊩ε (Γ ∙ γ) = ⊩τvar γ , ⊩ε-weaken Γ (step (same Γ)) (Γ⊩ε Γ)

{- definition of the evaluation function -}

lookup : ∀ {Γ Δ σ ρ} (pr : σ ∈ Γ) → Δ ⊩ε Γ [ ρ ] → Δ ⊩τ σ [ get pr ρ ]
lookup {ε} () vs
lookup {_ ∙ σ} here! (v , _) = v
lookup {Γ ∙ _} (there pr) (v , vs) = lookup pr vs

vapp : ∀ {Γ τ σ f x} (vf : Γ ⊩τ σ ▹ τ [ f ]) (vx : Γ ⊩τ σ [ x ]) → Γ ⊩τ τ [ app f x ]
vapp {Γ} {τ} {σ} {f} {x} vf vx = coerce (λ f → Γ ⊩τ τ [ app f x ]) (weaken-same f) (vf (same Γ) vx)

eval : ∀ {Γ Δ} {σ} (t : Γ ⊢ σ) {ρ : Δ ⊩ Γ} (vs : Δ ⊩ε Γ [ ρ ]) → Δ ⊩τ σ [ subst t ρ ]
eval (var pr) vs = lookup pr vs
eval {Γ} {Δ} {σ ▹ τ} (lam t) {ρ} vs = λ {Ε} {s} inc v →
{- the model is closed under computations -}
  ⊩τ-◃ (red (weaken (pop! inc) (subst t (var here! , ⊩-weaken Γ (step (same Δ)) ρ))) s)
{- administrative bullshit -}
  (coerce (λ t → Ε ⊩τ τ [ t ]) (sym (trans (cong (λ t → subst t (s , Γ⊩ Ε))
  (weaken-subst (pop! inc) t (var here! , ⊩-weaken Γ (step (same Δ)) ρ)))
  (trans (cong (λ ρ → β-reduce (subst t (var here! , ρ)) s)
  (trans (⊩-weaken² Γ (step (same Δ)) (pop! inc) ρ)
  (trans (cong (λ pr → ⊩-weaken Γ pr ρ) (⊆-step-same inc))
  (sym (⊩-weaken² Γ inc (step (same Ε)) ρ))))) (βsubst t s (⊩-weaken Γ inc ρ)))))
{- the actual computation -}
  (eval t (v , (⊩ε-weaken Γ inc vs))))
eval (app t u) vs = vapp (eval t vs) (eval u vs)

εeval : ∀ {Δ Ε} Γ (e : Δ ⊩ Γ) {ρ : Ε ⊩ Δ} (vs : Ε ⊩ε Δ [ ρ ]) → Ε ⊩ε Γ [ ⊩² Γ e ρ ]
εeval ε e vs = tt
εeval (Γ ∙ σ) (t , e) vs = eval t vs , εeval Γ e vs

quotient : ∀ {Γ σ} (t : Γ ⊢ σ) → Γ ⊩τ σ [ t ]
quotient {Γ} {σ} t = coerce (λ t → Γ ⊩τ σ [ t ]) (subst-Γ⊩ t) (eval t (Γ⊩ε Γ))

{- normalization: coming back from the model -}

to-the-future : ∀ {Γ σ} (t : Γ ⊢ σ) → Γ ⊢nf σ
to-the-future t = ↑ (quotient t)

norm : ∀ {Γ σ} (t : Γ ⊢ σ) → Γ ⊢ σ
norm = back-nf ∘ to-the-future

{-------------------------------------------------}
{-------- Properties of these definitions --------}
{-------------------------------------------------}

{- normalizing gives you back a reduct of the original term -}

norm-reduces : ∀ {Γ σ} (t : Γ ⊢ σ) → t ▹⋆ norm t
norm-reduces t = ↑▹⋆ _ t (quotient t)

soundness : ∀ {Γ σ} (t u : Γ ⊢ σ) (pr : norm t ≡ norm u) → t ≡βη u
soundness t u pr =
  ≡⋆-trans (▹≡⋆ (norm-reduces t)) (≡⋆-sym (coerce (_≡βη_ u) (sym pr) (▹≡⋆ (norm-reduces u))))
