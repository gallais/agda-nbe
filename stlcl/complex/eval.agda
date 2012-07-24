module stlcl.complex.eval where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

open import tools.contexts
open import tools.closures
open import stlcl.definition
open import stlcl.reductions
open import stlcl.complex.model

vappend : ∀ {Δ σ xs ys} (XS : Δ ⊩ `list σ [ xs ]) (YS : Δ ⊩ `list σ [ ys ]) →
          Δ ⊩ `list σ [ xs `++ ys ]
vappend (`[] r) YS = ⊩-↝⋆ _ (▹⋆-trans (▹⋆-cong `++₁ r) (step `β++₁ refl)) YS
vappend (HD `∷ XS by r) YS = HD `∷ vappend XS YS by ▹⋆-trans (▹⋆-cong `++₁ r) (step `β++₂ refl)
vappend (mappend F xs YS r) ZS =
  mappend F xs (vappend YS ZS) (▹⋆-trans (▹⋆-cong `++₁ r) (step (`η++₂ _ _ _) refl))

vmap : ∀ {Δ σ τ f xs} (F : Δ ⊩ σ `→ τ [ f ]) (XS : Δ ⊩ `list σ [ xs ]) → Δ ⊩ `list τ [ `map f xs ]
vmap F (`[] r) = `[] (▹⋆-trans (▹⋆-cong `map₂ r) (step `βmap₁ refl))
vmap {Δ} {σ} {τ} {f} F (_`∷_by_ {hd} HD XS r) =
  F (same _) HD (≡-step (cong (λ s → s `$ hd) (sym (⊢-weaken-refl f))) refl)
  `∷ vmap F XS by ▹⋆-trans (▹⋆-cong `map₂ r) (step `βmap₂ refl)
vmap F (mappend G xs YS r) =
  mappend
  (λ {Ε} inc t → ⊩-↝⋆ _ (step `βλ (≡-step (cong₂ (λ g f → g `$ (f `$ back-ne t))
    (sym (subst-pop _ (back-ne t) inc)) (sym (subst-pop _ (back-ne t) inc))) refl))
    (F inc (G inc t) refl))
  xs (vmap F YS)
  (▹⋆-trans (▹⋆-cong `map₂ r) (step (`ηmap₂ _ _) (step (`++₁ (`ηmap₃ _ _ _)) refl)))

vfold : ∀ {Δ σ τ c n xs} (C : Δ ⊩ σ `→ τ `→ τ [ c ]) (N : Δ ⊩ τ [ n ])
        (XS : Δ ⊩ `list σ [ xs ]) → Δ ⊩ τ [ `fold c n xs ]
vfold C N (`[] r) = ⊩-↝⋆ _ (▹⋆-trans (▹⋆-cong `fold₃ r) (step `βfold₁ refl)) N
vfold {Δ} {σ} {τ} {c} {n} C N (_`∷_by_ {hd} {tl} HD XS r) =
  C (same _) HD (≡-step (cong (λ c → c `$ hd) (sym (⊢-weaken-refl _))) refl)
  (same _) (vfold C N XS) (▹⋆-trans (▹⋆-cong `fold₃ r) (step `βfold₂ (≡-step
  (cong₂ (λ f x → f `$ x `$ `fold c n tl) (sym (⊢-weaken-refl c)) (sym (⊢-weaken-refl hd))) refl)))
vfold {Δ} {σ} {τ} {c} {n} C N (mappend F xs {ys} YS r) =
  ⊩-↝⋆ _ (▹⋆-trans (▹⋆-cong `fold₃ r) (step (`ηfold₁ _ _) (step (`ηfold₂ _ _ _)
  (▹⋆-trans (▹⋆-cong {f = λ f → `fold (`λ f) (`fold c n ys) (back-ne xs)} (λ r → `fold₁ (`λ r))
  (step (`ηλ _) (▹⋆-cong {f = `λ} `λ (≡-step
  (cong₂ (λ c f → c `$ (f `$ `v (there here!)) `$ `v here!)
   (trans (⊢-weaken² _ _ c) (sym (⊢-weaken² _ _ c)))
   (trans (⊢-weaken² _ _ _) (sym (⊢-weaken² _ _ _))))
  ([ _ ] _ ↝⋆↑ _)))))
  (▹⋆-cong `fold₂ ([ _ ] _ ↝⋆↑ _))))))
  (↓[ _ ] `fold
    (`λ (`λ (↑[ _ ] C (step (step (same _))) (F (step (step (same _))) (`v (there here!))) refl
                      (same _)               (↓[ _ ] `v here!)                             refl)))
    (↑[ _ ] vfold C N YS) xs)

lookup : ∀ Γ {Δ σ} (pr : σ ∈ Γ) {ρ} (vs : Δ ⊩ε Γ [ ρ ]) → Δ ⊩ σ [ get pr ρ ]
lookup ε () vs
lookup (Γ ∙ σ) here! (_ , v) = v
lookup (Γ ∙ σ) (there pr) (vs , _) = lookup Γ pr vs

eval : ∀ {Γ σ Δ} (t : Γ ⊢ σ) {ρ} (vs : Δ ⊩ε Γ [ ρ ]) → Δ ⊩ σ [ subst t ρ ]
eval (`v pr) vs = lookup _ pr vs
eval {Γ} (`λ t) {ρ} vs =
  λ {Ε} inc {s} S {ts} r → ⊩-↝⋆ _ (▹⋆-trans r (step `βλ (≡-step (trans
  (subst-weaken (pop! inc) (subst t (_ , `v here!)) (⊢ε-refl Ε , s)) (trans
  (subst² t _ (purge inc (⊢ε-refl Ε) , s)) (cong (λ ρ → subst t (ρ , s))
  (trans (⊢ε²-step Γ _ _ s) (trans (cong (⊢ε² Γ ρ) (purge-⊢ε-refl inc))
  (trans (sym (⊢ε²-weaken Γ inc _ _)) (cong (⊢ε-weaken Γ inc) (⊢ε²-refl Γ ρ)))))))) refl)))
  (eval t (⊩ε-weaken Γ inc vs , S))
eval (f `$ x) {ρ} vs =
  eval f vs (same _) (eval x vs)
  (≡-step (cong (λ t → t `$ subst x ρ) (sym (⊢-weaken-refl (subst f ρ)))) refl)
eval `⟨⟩ vs = tt
eval (a `, b) vs = _ , _ , refl , eval a vs , eval b vs
eval (`π₁ t) vs with eval t vs
... | a , b , r , A , B = ⊩-↝⋆ _ (▹⋆-trans (▹⋆-cong `π₁ r) (step `βπ₁ refl)) A
eval (`π₂ t) vs with eval t vs
... | a , b , r , A , B = ⊩-↝⋆ _ (▹⋆-trans (▹⋆-cong `π₂ r) (step `βπ₂ refl)) B
eval `[] vs = `[] refl
eval (hd `∷ tl) vs = eval hd vs `∷ eval tl vs by refl
eval (xs `++ ys) vs = vappend (eval xs vs) (eval ys vs)
eval (`map f xs) vs = vmap (eval f vs) (eval xs vs)
eval (`fold c n xs) vs = vfold (eval c vs) (eval n vs) (eval xs vs)

norm : ∀ {Γ σ} (t : Γ ⊢ σ) → Γ ⊢ σ
norm {Γ} {σ} t = back-nf (↑[ σ ] eval t (⊩ε-refl Γ))

soundness : ∀ {Γ σ} t → Γ ⊢ σ ∋ t ↝⋆ norm t
soundness t = ≡-step (sym (subst-refl t)) ([ _ ] _ ↝⋆↑ _)
