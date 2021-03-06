module stlcl.simple.eval where

open import Data.Nat
open import Data.Fin
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

open import tools.contexts
open import tools.closures
open import stlcl.definition
open import stlcl.normalforms
open import stlcl.simple.model

vappend : ∀ {n Δ} (σ : ty n) (XS : Δ ⊩ `list σ) (YS : Δ ⊩ `list σ) → Δ ⊩ `list σ
vappend σ `[] YS = YS
vappend σ (HD `∷ XS) YS = HD `∷ vappend σ XS YS
vappend σ (mappend F xs YS) ZS = mappend F xs (vappend σ YS ZS)

vmap : ∀ {n Δ} (σ τ : ty n) (F : Δ ⊩ σ `→ τ) (XS : Δ ⊩ `list σ) → Δ ⊩ `list τ
vmap σ τ F `[] = `[]
vmap σ τ F (HD `∷ TL) = F (same _) HD `∷ vmap σ τ F TL
vmap σ τ F (mappend G xs YS) = mappend (λ {Ε} inc t → F inc (G inc t)) xs (vmap σ τ F YS)

vfold : ∀ {n Δ} (σ τ : ty n) (C : Δ ⊩ σ `→ τ `→ τ) (N : Δ ⊩ τ) (XS : Δ ⊩ `list σ) → Δ ⊩ τ
vfold σ τ C N `[] = N
vfold σ τ C N (HD `∷ TL) = C (same _) HD (same _) (vfold σ τ C N TL)
vfold {Δ = Δ} σ τ C N (mappend F xs YS) =
  ↓[ τ ] `fold
    (`λ (`λ (↑[ τ ] C (step (step (same Δ))) (F (step (step (same _))) (`v (there here!)))
                      (same _) (↓[ τ ] `v here!))))
    (↑[ _ ] vfold σ τ C N YS) xs

lookup : ∀ {n} Γ {Δ} {σ : ty n} (pr : σ ∈ Γ) (R : Δ ⊩ε Γ) → Δ ⊩ σ
lookup ε () vs
lookup (Γ ∙ σ) here! (_ , v) = v
lookup (Γ ∙ σ) (there pr) (vs , _) = lookup Γ pr vs

eval : ∀ {n Γ Δ} {σ : ty n} (t : Γ ⊢ σ) (vs : Δ ⊩ε Γ) → Δ ⊩ σ
eval (`v pr) vs = lookup _ pr vs
eval {Γ = Γ} (`λ t) vs = λ {Ε} inc S → eval t (⊩ε-weaken Γ inc vs , S)
eval (f `$ x) vs = eval f vs (same _) (eval x vs)
eval `⟨⟩ vs = tt
eval (a `, b) vs = eval a vs , eval b vs
eval (`π₁ t) vs = proj₁ (eval t vs)
eval (`π₂ t) vs = proj₂ (eval t vs)
eval `[] vs = `[]
eval (hd `∷ tl) vs = eval hd vs `∷ eval tl vs
eval {_} {Γ} {Δ} {`list σ} (xs `++ ys) vs = vappend σ (eval xs vs) (eval ys vs)
eval {_} {Γ} {Δ} {`list τ} (`map {σ} f xs) vs = vmap σ τ (eval f vs) (eval xs vs)
eval {Γ = Γ} {σ = τ} (`fold {σ} c n xs) vs = vfold σ τ (eval c vs) (eval n vs) (eval xs vs)

εeval : ∀ {n} Γ {Δ Ε : Con (ty n)} (ρ : Δ ⊢ε Γ) (vs : Ε ⊩ε Δ) → Ε ⊩ε Γ
εeval ε ρ vs = ρ
εeval (Γ ∙ σ) (ρ , r) vs = εeval Γ ρ vs , eval r vs

norm : ∀ {n Γ} {σ : ty n} (t : Γ ⊢ σ) → Γ ⊢ σ
norm {_} {Γ} {σ} t = back-nf (↑[ σ ] eval t (⊩ε-refl Γ))