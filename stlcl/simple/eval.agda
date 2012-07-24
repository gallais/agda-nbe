module stlcl.simple.eval where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

open import tools.contexts
open import tools.closures
open import stlcl.definition
open import stlcl.reductions
open import stlcl.simple.model

vappend : ∀ {Δ σ} (XS : Δ ⊩ `list σ) (YS : Δ ⊩ `list σ) → Δ ⊩ `list σ
vappend `[] YS = YS
vappend {Δ} {σ} (HD `∷ XS) YS = HD `∷ vappend {Δ} {σ} XS YS
vappend {Δ} {σ} (mappend F xs YS) ZS = mappend F xs (vappend {Δ} {σ} YS ZS)

vmap : ∀ {Δ σ τ} (F : Δ ⊩ σ `→ τ) (XS : Δ ⊩ `list σ) → Δ ⊩ `list τ
vmap F `[] = `[]
vmap {Δ} {σ} {τ} F (HD `∷ TL) = F (same _) HD `∷ vmap {Δ} {σ} {τ} F TL
vmap {Δ} {σ} {τ} F (mappend G xs YS) =
  mappend (λ {Ε} inc t → F inc (G inc t)) xs (vmap {Δ} {σ} {τ} F YS)

vfold : ∀ {Δ σ τ} (C : Δ ⊩ σ `→ τ `→ τ) (N : Δ ⊩ τ) (XS : Δ ⊩ `list σ) → Δ ⊩ τ
vfold C N `[] = N
vfold {Δ} {σ} {τ} C N (HD `∷ TL) = C (same _) HD (same _) (vfold {Δ} {σ} {τ} C N TL)
vfold {Δ} {σ} {τ} C N (mappend F xs YS) =
  ↓[ τ ] `fold
    (`λ (`λ (↑[ τ ] C (step (step (same Δ))) (F (step (step (same _))) (`v (there here!)))
                      (same _) (↓[ τ ] `v here!))))
    (↑[ _ ] vfold {Δ} {σ} {τ} C N YS) xs

lookup : ∀ Γ {Δ σ} (pr : σ ∈ Γ) (R : Δ ⊩ε Γ) → Δ ⊩ σ
lookup ε () vs
lookup (Γ ∙ σ) here! (_ , v) = v
lookup (Γ ∙ σ) (there pr) (vs , _) = lookup Γ pr vs

eval : ∀ {Γ σ Δ} (t : Γ ⊢ σ) (vs : Δ ⊩ε Γ) → Δ ⊩ σ
eval (`v pr) vs = lookup _ pr vs
eval {Γ} (`λ t) vs = λ {Ε} inc S → eval t (⊩ε-weaken Γ inc vs , S)
eval (f `$ x) vs = eval f vs (same _) (eval x vs)
eval `⟨⟩ vs = tt
eval (a `, b) vs = eval a vs , eval b vs
eval (`π₁ t) vs = proj₁ (eval t vs)
eval (`π₂ t) vs = proj₂ (eval t vs)
eval `[] vs = `[]
eval (hd `∷ tl) vs = eval hd vs `∷ eval tl vs
eval {Γ} {`list σ} {Δ} (xs `++ ys) vs = vappend {Δ} {σ} (eval xs vs) (eval ys vs)
eval {Γ} {`list τ} {Δ} (`map {σ} f xs) vs = vmap {Δ} {σ} {τ} (eval f vs) (eval xs vs)
eval {Γ} {τ} {Δ} (`fold {σ} c n xs) vs = vfold {Δ} {σ} {τ} (eval c vs) (eval n vs) (eval xs vs)

norm : ∀ {Γ σ} (t : Γ ⊢ σ) → Γ ⊢ σ
norm {Γ} {σ} t = back-nf (↑[ σ ] eval t (⊩ε-refl Γ))