module stlc.reductions where

open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

open import tools.contexts
open import tools.closures
open import stlc.definition

data _⊢ne_∋_ (Γ : Con ty) (τ : ty) : Γ ⊢ τ → Set where 
  var : (pr : τ ∈ Γ) → Γ ⊢ne τ ∋ var pr
  app : ∀ {σ t} (tne : Γ ⊢ne σ ▹ τ ∋ t) {u : Γ ⊢ σ} → Γ ⊢ne τ ∋ app t u

data _⊢_∋_▹_ (Γ : Con ty) : (τ : ty) (s t : Γ ⊢ τ) → Set where
  lam : ∀ {σ τ s t} (r : Γ ∙ σ ⊢ τ ∋ s ▹ t) → Γ ⊢ σ ▹ τ ∋ lam s ▹ lam t
  eta : ∀ {σ τ t} → Γ ⊢ σ ▹ τ ∋ t ▹ η-expand t
  apl : ∀ {σ τ f g s} (r : Γ ⊢ σ ▹ τ ∋ f ▹ g) →  Γ ⊢ τ ∋ app f s ▹ app g s
  apr : ∀ {σ τ f s t} (r : Γ ⊢ σ ∋ s ▹ t) →  Γ ⊢ τ ∋ app f s ▹ app f t
  red : ∀ {σ τ} t (s : Γ ⊢ σ) → Γ ⊢ τ ∋ app (lam t) s ▹ β-reduce t s

_▹⋆_ : ∀ {Γ τ} (s t : Γ ⊢ τ) → Set
_▹⋆_ {Γ} {τ} s t = s ▹[ _⊢_∋_▹_ Γ τ ]⋆ t

_≡βη_ : ∀ {Γ τ} (s t : Γ ⊢ τ) → Set
_≡βη_ {Γ} {τ} s t = s ≡[ _⊢_∋_▹_ Γ τ ]⋆ t

{-------------------------------------------------}
{-------- Properties of these definitions --------}
{-------------------------------------------------}

{- all the possible weakenings -}

⊢ne-weaken : ∀ {Γ Δ σ t} (inc : Γ ⊆ Δ) (pr : Γ ⊢ne σ ∋ t) → Δ ⊢ne σ ∋ weaken inc t
⊢ne-weaken inc (var pr) = var (inc-in inc pr)
⊢ne-weaken inc (app tne) = app (⊢ne-weaken inc tne)

▹-weaken : ∀ {Γ Δ τ s t} (pr : Γ ⊆ Δ) (r : Γ ⊢ τ ∋ s ▹ t) →
           Δ ⊢ τ ∋ weaken pr s ▹ weaken pr t
▹-weaken pr (lam r) = lam (▹-weaken (pop! pr) r)
▹-weaken pr (eta {σ} {τ} {t}) rewrite η-weaken pr t = eta
▹-weaken pr (apl r) = apl (▹-weaken pr r)
▹-weaken pr (apr r) = apr (▹-weaken pr r)
▹-weaken {Γ} {Δ} {τ} pr (red t s) rewrite β-weaken pr t s = red (weaken (pop! pr) t) (weaken pr s)

{- weakening and reduction commute -}

▹w : ∀ {Γ Δ τ} {inc : Γ ⊆ Δ} {s : Γ ⊢ τ} {s' t : Δ ⊢ τ} (Heq : s' ≡ weaken inc s)
     (r : Δ ⊢ τ ∋ s' ▹ t) → Σ (Γ ⊢ τ) (λ t' → t ≡ weaken inc t')
▹w Heq (lam r) with lam-w _ Heq
... | s , refl with ▹w (lam-eq Heq) r
... | t' , Ht' = lam t' , cong lam Ht'
▹w Heq (apl r) with app-w _ Heq
... | f , x , refl with ▹w (appl-eq Heq) r
... | t' , Ht' = app t' x , cong₂ app Ht' (appr-eq Heq)
▹w Heq (apr r) with app-w _ Heq
... | f , x , refl with ▹w (appr-eq Heq) r
... | t' , Ht' = app f t' , cong₂ app (appl-eq Heq) Ht'
▹w Heq (red t u) with app-w _ Heq
... | f , x , refl with lam-w f (appl-eq Heq)
... | t' , Ht' = β-reduce t' x ,
  trans (cong₂ β-reduce (lam-eq (trans (appl-eq Heq) (cong (weaken _) Ht'))) (appr-eq Heq))
        (sym (β-weaken _ t' x))
▹w {Γ} {Δ} {σ ▹ τ} {inc} {s} refl eta = η-expand s ,
  cong (λ t → lam (app t (var here!))) (trans (weaken² inc (step (same _)) s)
  (trans (cong (λ pr → weaken pr s) (sym (⊆-step-same inc)))
  (sym (weaken² (step (same _)) (pop! inc) s))))

▹⋆w : ∀ {Γ Δ τ} {inc : Γ ⊆ Δ} {s : Γ ⊢ τ} {t : Δ ⊢ τ} (r : weaken inc s ▹⋆ t) →
      Σ (Γ ⊢ τ) (λ t' → t ≡ weaken inc t')
▹⋆w refl = _ , refl
▹⋆w (step p r) with ▹w refl p
... | _ , refl = ▹⋆w r