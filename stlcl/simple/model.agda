module stlcl.simple.model where

open import Data.Nat
open import Data.Fin
open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

open import tools.contexts
open import tools.closures
open import stlcl.definition
open import stlcl.normalforms

infix 5 _⊩_

data _⊩list_ {n} (Γ : Con (ty n)) (Σ : Con (ty n) → Set) : Set where
  `[] : Γ ⊩list Σ
  _`∷_ : ∀ (HD : Σ Γ) (TL : Γ ⊩list Σ) → Γ ⊩list Σ
  mappend :
   ∀ {τ} (F : ∀ {Δ} (inc : Γ ⊆ Δ) (t : Δ ⊢ne τ) → Σ Δ) (xs : Γ ⊢ne `list τ)
   (YS : Γ ⊩list Σ) → Γ ⊩list Σ

_⊩_ : ∀ {n} Γ (σ : ty n) → Set
Γ ⊩ `1 = ⊤
Γ ⊩ `b k = Γ ⊢ne `b k
Γ ⊩ σ `× τ = Γ ⊩ σ × Γ ⊩ τ
Γ ⊩ σ `→ τ = ∀ {Δ} (inc : Γ ⊆ Δ) (v : Δ ⊩ σ) → Δ ⊩ τ
Γ ⊩ `list σ = Γ ⊩list (λ Δ → Δ ⊩ σ)

⊩-weaken : ∀ {n} (σ : ty n) {Γ Δ} (inc : Γ ⊆ Δ) (T : Γ ⊩ σ) → Δ ⊩ σ
⊩-weaken `1 inc T = tt
⊩-weaken (`b k) inc T = ne-weaken inc T
⊩-weaken (σ `× τ) inc (A , B) = ⊩-weaken σ inc A , ⊩-weaken τ inc B
⊩-weaken (σ `→ τ) inc T = λ {Ε} inc' S → T (⊆-trans inc inc') S
⊩-weaken (`list σ) inc `[] = `[]
⊩-weaken (`list σ) inc (HD `∷ TL) = ⊩-weaken σ inc HD `∷ ⊩-weaken (`list σ) inc TL
⊩-weaken (`list σ) inc (mappend F xs YS) =
  mappend (λ {Ε} inc' t → F (⊆-trans inc inc') t) (ne-weaken inc xs) (⊩-weaken (`list σ) inc YS)

↑list[_]_ : ∀ {n Γ} {σ : ty n} (Σ : ∀ {Δ : Con (ty n)} (S : Δ ⊩ σ) → Δ ⊢nf σ)
  (XS : Γ ⊩ `list σ) → Γ ⊢nf `list σ
↑list[ Σ ] `[] = `[]
↑list[ Σ ] (HD `∷ TL) = Σ HD `∷ ↑list[ Σ ] TL
↑list[ Σ ] mappend F xs YS = mappend (`λ (Σ (F (step (same _)) (`v here!)))) xs (↑list[ Σ ] YS)

mutual

  ↑[_]_ : ∀ {n} (σ : ty n) {Γ} (S : Γ ⊩ σ) → Γ ⊢nf σ
  ↑[ `1 ] T = `⟨⟩
  ↑[ `b k ] T = `↑ T
  ↑[ σ `× τ ] (A , B) = ↑[ σ ] A `, ↑[ τ ] B
  ↑[ σ `→ τ ] T = `λ (↑[ τ ] T (step (same _)) (↓[ σ ] `v here!))
  ↑[ `list σ ] T = ↑list[ ↑[_]_ σ ] T

  ↓[_]_ : ∀ {n} (σ : ty n) {Γ} (s : Γ ⊢ne σ) → Γ ⊩ σ
  ↓[ `1 ] t = tt
  ↓[ `b k ] t = t
  ↓[ σ `× τ ] t = ↓[ σ ] `π₁ t , ↓[ τ ] `π₂ t
  ↓[ σ `→ τ ] t = λ {Δ} inc S → (↓[ τ ] (ne-weaken inc t `$ ↑[ σ ] S))
  ↓[ `list σ ] t = mappend (λ _ t → ↓[ σ ] t) t `[]

_⊩ε_ : ∀ {n} (Δ Γ : Con (ty n)) → Set
Δ ⊩ε ε = ⊤
Δ ⊩ε Γ ∙ σ = Δ ⊩ε Γ × Δ ⊩ σ

⊩ε-weaken : ∀ {n} Γ {Δ Ε : Con (ty n)} (inc : Δ ⊆ Ε) (vs : Δ ⊩ε Γ) → Ε ⊩ε Γ
⊩ε-weaken ε inc vs = vs
⊩ε-weaken (Γ ∙ σ) inc (vs , v) = ⊩ε-weaken Γ inc vs , ⊩-weaken σ inc v

⊩ε-refl : ∀ {n} (Γ : Con (ty n)) → Γ ⊩ε Γ
⊩ε-refl ε = tt
⊩ε-refl (Γ ∙ σ) = ⊩ε-weaken Γ (step (same _)) (⊩ε-refl Γ) , ↓[ σ ] `v here!

⊩ε-purge : ∀ {n} {Γ Δ Ε : Con (ty n)} (inc : Γ ⊆ Δ) (R : Ε ⊩ε Δ) → Ε ⊩ε Γ
⊩ε-purge base R = tt
⊩ε-purge (step inc) (R , _) = ⊩ε-purge inc R
⊩ε-purge (pop! inc) (R , r) = ⊩ε-purge inc R , r

abstract

  ⊩ε-purge-refl : ∀ {n} Γ {Δ : Con (ty n)} (R : Δ ⊩ε Γ) → ⊩ε-purge (same Γ) R ≡ R
  ⊩ε-purge-refl ε R = refl
  ⊩ε-purge-refl (Γ ∙ σ) (R , r) rewrite ⊩ε-purge-refl Γ R = refl

  ⊩ε-purge² : ∀ {n} {Γ Δ : Con (ty n)} (inc : Γ ⊆ Δ) {Ε} (inc' : Δ ⊆ Ε) {Φ} (R : Φ ⊩ε Ε) →
    ⊩ε-purge inc (⊩ε-purge inc' R) ≡ ⊩ε-purge (⊆-trans inc inc') R
  ⊩ε-purge² base base R = refl
  ⊩ε-purge² base (step inc) (R , _) = ⊩ε-purge² base inc R
  ⊩ε-purge² (step inc) (step inc') (R , _) = ⊩ε-purge² (step inc) inc' R
  ⊩ε-purge² (step inc) (pop! inc') (R , _) = ⊩ε-purge² inc inc' R
  ⊩ε-purge² (pop! inc) (step inc') (R , _) = ⊩ε-purge² (pop! inc) inc' R
  ⊩ε-purge² (pop! inc) (pop! inc') (R , r) rewrite ⊩ε-purge² inc inc' R = refl

  ⊩ε-purge-weaken : ∀ {n} {Γ Δ : Con (ty n)} (inc : Γ ⊆ Δ) {Ε Φ} (inc' : Ε ⊆ Φ) (R : Ε ⊩ε Δ) →
    ⊩ε-purge inc (⊩ε-weaken Δ inc' R) ≡ ⊩ε-weaken Γ inc' (⊩ε-purge inc R)
  ⊩ε-purge-weaken base inc' R = refl
  ⊩ε-purge-weaken (step inc) inc' (R , _) = ⊩ε-purge-weaken inc inc' R
  ⊩ε-purge-weaken (pop! inc) inc' (R , r) rewrite ⊩ε-purge-weaken inc inc' R = refl