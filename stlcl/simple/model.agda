module stlcl.simple.model where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

open import tools.contexts
open import tools.closures
open import stlcl.definition

infix 5 _⊢ne_ _⊢nf_ _⊩_

mutual

  data _⊢ne_ (Γ : Con ty) (τ : ty) : Set where
    `v : ∀ (pr : τ ∈ Γ) → Γ ⊢ne τ
    _`$_ : ∀ {σ} (t : Γ ⊢ne σ `→ τ) (u : Γ ⊢nf σ) → Γ ⊢ne τ
    `π₁ : ∀ {σ} (p : Γ ⊢ne τ `× σ) → Γ ⊢ne τ
    `π₂ : ∀ {σ} (p : Γ ⊢ne σ `× τ) → Γ ⊢ne τ
    `fold : ∀ {σ} (c : Γ ⊢nf σ `→ τ `→ τ) (n : Γ ⊢nf τ) (xs : Γ ⊢ne `list σ) → Γ ⊢ne τ

  data _⊢nf_ (Γ : Con ty) : ty → Set where
    `λ : ∀ {σ τ} (t : Γ ∙ σ ⊢nf τ) → Γ ⊢nf σ `→ τ
    `⟨⟩ : Γ ⊢nf `1
    _`,_ : ∀ {σ τ} (a : Γ ⊢nf σ) (b : Γ ⊢nf τ) → Γ ⊢nf σ `× τ
    `[] : ∀ {σ} → Γ ⊢nf `list σ
    _`∷_ : ∀ {σ} (hd : Γ ⊢nf σ) (tl : Γ ⊢nf `list σ) → Γ ⊢nf `list σ
    mappend : ∀ {σ τ} (f : Γ ⊢nf σ `→ τ) (xs : Γ ⊢ne `list σ)
              (ys : Γ ⊢nf `list τ) → Γ ⊢nf `list τ

mutual

  back-ne : ∀ {Γ σ} (t : Γ ⊢ne σ) → Γ ⊢ σ
  back-ne (`v pr) = `v pr
  back-ne (t `$ u) = back-ne t `$ back-nf u
  back-ne (`π₁ t) = `π₁ (back-ne t)
  back-ne (`π₂ t) = `π₂ (back-ne t)
  back-ne (`fold c n xs) = `fold (back-nf c) (back-nf n) (back-ne xs)

  back-nf : ∀ {Γ σ} (t : Γ ⊢nf σ) → Γ ⊢ σ
  back-nf (`λ t) = `λ (back-nf t)
  back-nf `⟨⟩ = `⟨⟩
  back-nf (a `, b) = back-nf a `, back-nf b
  back-nf `[] = `[]
  back-nf (hd `∷ tl) = back-nf hd `∷ back-nf tl
  back-nf (mappend f xs ys) = `map (back-nf f) (back-ne xs) `++ back-nf ys

mutual

  ne-weaken : ∀ {Γ Δ σ} (inc : Γ ⊆ Δ) (t : Γ ⊢ne σ) → Δ ⊢ne σ
  ne-weaken inc (`v pr) = `v (inc-in inc pr)
  ne-weaken inc (f `$ x) = ne-weaken inc f `$ nf-weaken inc x
  ne-weaken inc (`π₁ t) = `π₁ (ne-weaken inc t)
  ne-weaken inc (`π₂ t) = `π₂ (ne-weaken inc t)
  ne-weaken inc (`fold c n xs) = `fold (nf-weaken inc c) (nf-weaken inc n) (ne-weaken inc xs)

  nf-weaken : ∀ {Γ Δ σ} (inc : Γ ⊆ Δ) (t : Γ ⊢nf σ) → Δ ⊢nf σ
  nf-weaken inc (`λ t) = `λ (nf-weaken (pop! inc) t)
  nf-weaken inc `⟨⟩ = `⟨⟩
  nf-weaken inc (a `, b) = nf-weaken inc a `, nf-weaken inc b
  nf-weaken inc `[] = `[]
  nf-weaken inc (hd `∷ tl) = nf-weaken inc hd `∷ nf-weaken inc tl
  nf-weaken inc (mappend f xs ys) = mappend (nf-weaken inc f) (ne-weaken inc xs) (nf-weaken inc ys)

mutual

  ne-weaken-back : ∀ {Γ Δ σ} (inc : Γ ⊆ Δ) (t : Γ ⊢ne σ) →
                   back-ne (ne-weaken inc t) ≡ ⊢-weaken inc (back-ne t)
  ne-weaken-back inc (`v pr) = refl
  ne-weaken-back inc (f `$ x) = cong₂ _`$_ (ne-weaken-back inc f) (nf-weaken-back inc x)
  ne-weaken-back inc (`π₁ t) = cong `π₁ (ne-weaken-back inc t)
  ne-weaken-back inc (`π₂ t) = cong `π₂ (ne-weaken-back inc t)
  ne-weaken-back inc (`fold c n xs) =
    cong₃ `fold (nf-weaken-back inc c) (nf-weaken-back inc n) (ne-weaken-back inc xs)

  nf-weaken-back : ∀ {Γ Δ σ} (inc : Γ ⊆ Δ) (t : Γ ⊢nf σ) →
                   back-nf (nf-weaken inc t) ≡ ⊢-weaken inc (back-nf t)
  nf-weaken-back inc (`λ t) = cong `λ (nf-weaken-back (pop! inc) t)
  nf-weaken-back inc `⟨⟩ = refl
  nf-weaken-back inc (a `, b) = cong₂ _`,_ (nf-weaken-back inc a) (nf-weaken-back inc b)
  nf-weaken-back inc `[] = refl
  nf-weaken-back inc (hd `∷ tl) = cong₂ _`∷_ (nf-weaken-back inc hd) (nf-weaken-back inc tl)
  nf-weaken-back inc (mappend f xs ys) =
    cong₃ (λ f xs ys → `map f xs `++ ys) (nf-weaken-back inc f)
         (ne-weaken-back inc xs) (nf-weaken-back inc ys)

data _⊩list_ (Γ : Con ty) (Σ : Con ty → Set) : Set where
  `[] : Γ ⊩list Σ
  _`∷_ : ∀ (HD : Σ Γ) (TL : Γ ⊩list Σ) → Γ ⊩list Σ
  mappend :
   ∀ {τ} (F : ∀ {Δ} (inc : Γ ⊆ Δ) (t : Δ ⊢ne τ) → Σ Δ) (xs : Γ ⊢ne `list τ)
   (YS : Γ ⊩list Σ) → Γ ⊩list Σ

_⊩_ : ∀ Γ σ → Set
Γ ⊩ `1 = ⊤
Γ ⊩ σ `× τ = Γ ⊩ σ × Γ ⊩ τ
Γ ⊩ σ `→ τ = ∀ {Δ} (inc : Γ ⊆ Δ) (v : Δ ⊩ σ) → Δ ⊩ τ
Γ ⊩ `list σ = Γ ⊩list (λ Δ → Δ ⊩ σ)

⊩-weaken : ∀ σ {Γ Δ} (inc : Γ ⊆ Δ) (T : Γ ⊩ σ) → Δ ⊩ σ
⊩-weaken `1 inc T = tt
⊩-weaken (σ `× τ) inc (A , B) = ⊩-weaken σ inc A , ⊩-weaken τ inc B
⊩-weaken (σ `→ τ) inc T = λ {Ε} inc' S → T (⊆-trans inc inc') S
⊩-weaken (`list σ) inc `[] = `[]
⊩-weaken (`list σ) inc (HD `∷ TL) = ⊩-weaken σ inc HD `∷ ⊩-weaken (`list σ) inc TL
⊩-weaken (`list σ) inc (mappend F xs YS) =
  mappend (λ {Ε} inc' t → F (⊆-trans inc inc') t) (ne-weaken inc xs) (⊩-weaken (`list σ) inc YS)

↑list[_]_ : ∀ {σ Γ} (Σ : ∀ {Δ} (S : Δ ⊩ σ) → Δ ⊢nf σ) (XS : Γ ⊩ `list σ) → Γ ⊢nf `list σ
↑list[ Σ ] `[] = `[]
↑list[ Σ ] (HD `∷ TL) = Σ HD `∷ ↑list[ Σ ] TL
↑list[ Σ ] mappend F xs YS = mappend (`λ (Σ (F (step (same _)) (`v here!)))) xs (↑list[ Σ ] YS)

mutual

  ↑[_]_ : ∀ σ {Γ} (S : Γ ⊩ σ) → Γ ⊢nf σ
  ↑[ `1 ] T = `⟨⟩
  ↑[ σ `× τ ] (A , B) = ↑[ σ ] A `, ↑[ τ ] B
  ↑[ σ `→ τ ] T = `λ (↑[ τ ] T (step (same _)) (↓[ σ ] `v here!))
  ↑[ `list σ ] T = ↑list[ ↑[_]_ σ ] T

  ↓[_]_ : ∀ σ {Γ} (s : Γ ⊢ne σ) → Γ ⊩ σ
  ↓[ `1 ] t = tt
  ↓[ σ `× τ ] t = ↓[ σ ] `π₁ t , ↓[ τ ] `π₂ t
  ↓[ σ `→ τ ] t = λ {Δ} inc S → (↓[ τ ] (ne-weaken inc t `$ ↑[ σ ] S))
  ↓[ `list σ ] t = mappend (λ _ t → ↓[ σ ] t) t `[]

_⊩ε_ : ∀ (Δ Γ : Con ty) → Set
Δ ⊩ε ε = ⊤
Δ ⊩ε Γ ∙ σ = Δ ⊩ε Γ × Δ ⊩ σ

⊩ε-weaken : ∀ Γ {Δ Ε} (inc : Δ ⊆ Ε) (vs : Δ ⊩ε Γ) → Ε ⊩ε Γ
⊩ε-weaken ε inc vs = vs
⊩ε-weaken (Γ ∙ σ) inc (vs , v) = ⊩ε-weaken Γ inc vs , ⊩-weaken σ inc v

⊩ε-refl : (Γ : Con ty) → Γ ⊩ε Γ
⊩ε-refl ε = tt
⊩ε-refl (Γ ∙ σ) = ⊩ε-weaken Γ (step (same _)) (⊩ε-refl Γ) , ↓[ σ ] `v here!
