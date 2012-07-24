module stlcl.normalforms where

open import Relation.Binary.PropositionalEquality

open import tools.contexts
open import stlcl.definition

infix 5 _⊢ne_ _⊢nf_

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

  ne-weaken-refl : ∀ {Γ σ} (t : Γ ⊢ne σ) → ne-weaken (same Γ) t ≡ t
  ne-weaken-refl (`v pr) = cong `v (inc-in-same pr)
  ne-weaken-refl (t `$ u) = cong₂ _`$_ (ne-weaken-refl t) (nf-weaken-refl u)
  ne-weaken-refl (`π₁ t) = cong `π₁ (ne-weaken-refl t)
  ne-weaken-refl (`π₂ t) = cong `π₂ (ne-weaken-refl t)
  ne-weaken-refl (`fold c n t) = cong₃ `fold (nf-weaken-refl c) (nf-weaken-refl n) (ne-weaken-refl t)

  nf-weaken-refl : ∀ {Γ σ} (t : Γ ⊢nf σ) → nf-weaken (same Γ) t ≡ t
  nf-weaken-refl (`λ t) = cong `λ (nf-weaken-refl t)
  nf-weaken-refl `⟨⟩ = refl
  nf-weaken-refl (a `, b) = cong₂ _`,_ (nf-weaken-refl a) (nf-weaken-refl b)
  nf-weaken-refl `[] = refl
  nf-weaken-refl (hd `∷ tl) = cong₂ _`∷_ (nf-weaken-refl hd) (nf-weaken-refl tl)
  nf-weaken-refl (mappend f xs ys) =
    cong₃ mappend (nf-weaken-refl f) (ne-weaken-refl xs) (nf-weaken-refl ys)

mutual

  ne-weaken² : ∀ {Γ Δ} (inc : Γ ⊆ Δ) {Ε} (inc' : Δ ⊆ Ε) {σ} (t : Γ ⊢ne σ) →
    ne-weaken inc' (ne-weaken inc t) ≡ ne-weaken (⊆-trans inc inc') t
  ne-weaken² inc inc' (`v pr) = cong `v (inc-in² inc inc' pr)
  ne-weaken² inc inc' (t `$ u) = cong₂ _`$_ (ne-weaken² inc inc' t) (nf-weaken² inc inc' u)
  ne-weaken² inc inc' (`π₁ t) = cong `π₁ (ne-weaken² inc inc' t)
  ne-weaken² inc inc' (`π₂ t) = cong `π₂ (ne-weaken² inc inc' t)
  ne-weaken² inc inc' (`fold c n t) =
    cong₃ `fold (nf-weaken² inc inc' c) (nf-weaken² inc inc' n) (ne-weaken² inc inc' t)

  nf-weaken² : ∀ {Γ Δ} (inc : Γ ⊆ Δ) {Ε} (inc' : Δ ⊆ Ε) {σ} (t : Γ ⊢nf σ) →
    nf-weaken inc' (nf-weaken inc t) ≡ nf-weaken (⊆-trans inc inc') t
  nf-weaken² inc inc' (`λ t) = cong `λ (nf-weaken² (pop! inc) (pop! inc') t)
  nf-weaken² inc inc' `⟨⟩ = refl
  nf-weaken² inc inc' (a `, b) = cong₂ _`,_ (nf-weaken² inc inc' a) (nf-weaken² inc inc' b)
  nf-weaken² inc inc' `[] = refl
  nf-weaken² inc inc' (hd `∷ tl) = cong₂ _`∷_ (nf-weaken² inc inc' hd) (nf-weaken² inc inc' tl)
  nf-weaken² inc inc' (mappend f xs ys) =
    cong₃ mappend (nf-weaken² inc inc' f) (ne-weaken² inc inc' xs) (nf-weaken² inc inc' ys)

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