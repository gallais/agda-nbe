module stlc.eqdecide where

open import tools.contexts
open import tools.closures

open import stlc.definition
open import stlc.reductions
open import stlc.model
open import stlc.eval
open import stlc.complete

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

there-eq : ∀ {A Γ σ τ} {pr₁ pr₂ : σ ∈ Γ} (eq : there {A} {σ} {Γ} {τ} pr₁ ≡ there pr₂) → pr₁ ≡ pr₂
there-eq refl = refl

▹l-eq : ∀ {σ σ' τ τ'} (eq : σ ▹ τ ≡ σ' ▹ τ') → σ ≡ σ'
▹l-eq refl = refl

▹r-eq : ∀ {σ σ' τ τ'} (eq : σ ▹ τ ≡ σ' ▹ τ') → τ ≡ τ'
▹r-eq refl = refl

appty-eq : ∀ {Γ : Con ty} {σ σ' τ : ty} {f : Γ ⊢ σ ▹ τ} {g : Γ ⊢ σ' ▹ τ} {x : Γ ⊢ σ} {y : Γ ⊢ σ'} →
   _≡_ {_} {Γ ⊢ τ} (app f x) (app g y) → σ ≡ σ'
appty-eq refl = refl

∈≟ : ∀ {Γ} {σ : ty} (pr pr' : σ ∈ Γ) → Dec (pr ≡ pr')
∈≟ here! here! = yes refl
∈≟ here! (there pr') = no (λ ())
∈≟ (there pr) here! = no (λ ())
∈≟ (there pr) (there pr') with ∈≟ pr pr'
... | yes p = yes (cong there p)
... | no ¬p = no (λ p → ¬p (there-eq p))

ty-dec : ∀ (σ τ : ty) → Dec (σ ≡ τ)
ty-dec ♭ ♭ = yes refl
ty-dec ♭ (τσ ▹ ττ) = no (λ ())
ty-dec (σσ ▹ στ) ♭ = no (λ ())
ty-dec (σσ ▹ στ) (τσ ▹ ττ) with ty-dec σσ τσ | ty-dec στ ττ
... | yes p₁ | yes p₂ = yes (cong₂ _▹_ p₁ p₂)
... | no ¬p₁ | _ = no (λ p₁ → ¬p₁ (▹l-eq p₁))
... | _ | no ¬p₂ = no (λ p₂ → ¬p₂ (▹r-eq p₂))

_⊢_∋_≟_ : ∀ Γ σ (s t : Γ ⊢ σ) → Dec (s ≡ t)
Γ ⊢ σ ∋ var pr ≟ var pr' with ∈≟ pr pr'
... | yes p = yes (cong var p)
... | no ¬p = no (λ p → ¬p (var-eq p))
Γ ⊢ σ ▹ τ ∋ var pr ≟ lam t = no (λ ())
Γ ⊢ σ ∋ var pr ≟ app f x = no (λ ())
Γ ⊢ σ ▹ τ ∋ lam s ≟ var pr = no (λ ())
Γ ⊢ σ ▹ τ ∋ lam s ≟ lam t with Γ ∙ σ ⊢ τ ∋ s ≟ t
... | yes p = yes (cong lam p)
... | no ¬p = no (λ p → ¬p (lam-eq p))
Γ ⊢ σ ▹ τ ∋ lam s ≟ app f x = no (λ ())
Γ ⊢ σ ∋ app f x ≟ var pr = no (λ ())
Γ ⊢ σ ▹ τ ∋ app f x ≟ lam t = no (λ ())
Γ ⊢ τ ∋ app {σx} f x ≟ app {σy} g y with ty-dec σx σy
... | no ¬p = no (λ p → ¬p (appty-eq p))
Γ ⊢ τ ∋ app {.σ} f x ≟ app {σ} g y  | yes refl with Γ ⊢ _ ∋ f ≟ g | Γ ⊢ _ ∋ x ≟ y
... | yes p₁ | yes p₂ = yes (cong₂ app p₁ p₂)
... | no ¬p₁ | _ = no (λ p₁ → ¬p₁ (appl-eq p₁))
... | _ | no ¬p₂ = no (λ p₂ → ¬p₂ (appr-eq p₂))

_⊢_∋_≟βη_ : ∀ Γ σ (s t : Γ ⊢ σ) → Dec (s ≡βη t)
Γ ⊢ σ ∋ s ≟βη t with Γ ⊢ σ ∋ norm s ≟ norm t
... | yes p = yes (soundness s t p)
... | no ¬p = no (λ p → ¬p (completeness p))