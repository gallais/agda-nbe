module stlcl.reductions where

open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

open import tools.contexts
open import tools.closures
open import stlcl.definition

{- and their compatibility with weakening -}

η-weaken : ∀ {n Γ Δ} {σ τ : ty n} (pr : Γ ⊆ Δ) (t : Γ ⊢ σ `→ τ) →
           ⊢-weaken pr (η-expand t) ≡ η-expand (⊢-weaken pr t)
η-weaken pr t =
  cong (λ t → `λ (t `$ `v here!)) (trans (⊢-weaken² _ _ t)
  (trans (cong (λ pr → ⊢-weaken pr t) (⊆-step-same pr)) (sym (⊢-weaken² _ _ t))))

β-weaken : ∀ {n Γ Δ} {σ τ : ty n} (pr : Γ ⊆ Δ) (t : Γ ∙ σ ⊢ τ) (s : Γ ⊢ σ) →
           ⊢-weaken pr (β-reduce t s) ≡ β-reduce (⊢-weaken (pop! pr) t) (⊢-weaken pr s)
β-weaken {_} {Γ} {Δ} pr t s =
  trans (weaken-subst pr t (⊢ε-refl Γ , s)) (trans (cong (λ ρ → subst t (ρ , ⊢-weaken pr s))
  (sym (purge-⊢ε-refl pr))) (sym (subst-weaken (pop! pr) t (⊢ε-refl Δ , ⊢-weaken pr s))))

`∘-weaken : ∀ {n Γ Δ} {σ τ υ : ty n} (inc : Γ ⊆ Δ) (g : Γ ⊢ τ `→ υ) (f : Γ ⊢ σ `→ τ) →
            ⊢-weaken inc (g `∘ f) ≡ ⊢-weaken inc g `∘ ⊢-weaken inc f
`∘-weaken inc g f =
  cong₂ (λ g f → `λ (g `$ (f `$ `v here!)))
  (trans (⊢-weaken² _ (pop! inc) g) (trans (cong (λ pr → ⊢-weaken pr g)
    (⊆-step-same inc)) (sym (⊢-weaken² inc _ g))))
  (trans (⊢-weaken² _ (pop! inc) f) (trans (cong (λ pr → ⊢-weaken pr f)
    (⊆-step-same inc)) (sym (⊢-weaken² inc _ f))))

{- small step reduction relation -}

infix 5 _⊢_∋_↝_ _⊢_∋_↝⋆_ _⊢_∋_≅_

data _⊢_∋_↝_ {n} (Γ : Con (ty n)) : (τ : ty n) (s t : Γ ⊢ τ) → Set where
-- structural rules
  `λ : ∀ {σ τ s t} (r : Γ ∙ σ ⊢ τ ∋ s ↝ t) → Γ ⊢ σ `→ τ ∋ `λ s ↝ `λ t
  `$₁ : ∀ {σ τ f g x} (r : Γ ⊢ σ `→ τ ∋ f ↝ g) → Γ ⊢ τ ∋ f `$ x ↝ g `$ x
  `$₂ : ∀ {σ τ f x y} (r : Γ ⊢ σ ∋ x ↝ y) → Γ ⊢ τ ∋ f `$ x ↝ f `$ y
  `,₁ : ∀ {σ τ a c b} (r : Γ ⊢ σ ∋ a ↝ c) → Γ ⊢ σ `× τ ∋ a `, b ↝ c `, b
  `,₂ : ∀ {σ τ a b d} (r : Γ ⊢ τ ∋ b ↝ d) → Γ ⊢ σ `× τ ∋ a `, b ↝ a `, d
  `π₁ : ∀ {σ τ s t} (r : Γ ⊢ σ `× τ ∋ s ↝ t) → Γ ⊢ σ ∋ `π₁ s ↝ `π₁ t
  `π₂ : ∀ {σ τ s t} (r : Γ ⊢ σ `× τ ∋ s ↝ t) → Γ ⊢ τ ∋ `π₂ s ↝ `π₂ t
  `∷₁ : ∀ {σ fc hd tl} (r : Γ ⊢ σ ∋ fc ↝ hd) → Γ ⊢ `list σ ∋ fc `∷ tl ↝ hd `∷ tl
  `∷₂ : ∀ {σ hd sm tl} (r : Γ ⊢ `list σ ∋ sm ↝ tl) → Γ ⊢ `list σ ∋ hd `∷ sm ↝ hd `∷ tl
  `++₁ : ∀ {σ ws xs ys} (r : Γ ⊢ `list σ ∋ ws ↝ xs) → Γ ⊢ `list σ ∋ ws `++ ys ↝ xs `++ ys
  `++₂ : ∀ {σ xs ys zs} (r : Γ ⊢ `list σ ∋ ys ↝ zs) → Γ ⊢ `list σ ∋ xs `++ ys ↝ xs `++ zs
  `map₁ : ∀ {σ τ f g xs} (r : Γ ⊢ σ `→ τ ∋ f ↝ g) → Γ ⊢ `list τ ∋ `map f xs ↝ `map g xs
  `map₂ : ∀ {σ τ f xs ys} (r : Γ ⊢ `list σ ∋ xs ↝ ys) → Γ ⊢ `list τ ∋ `map f xs ↝ `map f ys
  `fold₁ : ∀ {σ τ c d n xs} (r : Γ ⊢ σ `→ τ `→ τ ∋ c ↝ d) → Γ ⊢ τ ∋ `fold c n xs ↝ `fold d n xs
  `fold₂ : ∀ {σ τ c m n xs} (r : Γ ⊢ τ ∋ m ↝ n) → Γ ⊢ τ ∋ `fold {σ = σ} c m xs ↝ `fold c n xs
  `fold₃ : ∀ {σ τ c n xs ys} (r : Γ ⊢ `list σ ∋ xs ↝ ys) → Γ ⊢ τ ∋ `fold c n xs ↝ `fold c n ys
-- beta laws
  `βλ : ∀ {σ τ t} {u : Γ ⊢ σ} → Γ ⊢ τ ∋ `λ t `$ u ↝ β-reduce t u
  `βπ₁ : ∀ {σ τ a} {b : Γ ⊢ τ} → Γ ⊢ σ ∋ `π₁ (a `, b) ↝ a
  `βπ₂ : ∀ {σ τ} {a : Γ ⊢ σ} {b} → Γ ⊢ τ ∋ `π₂ (a `, b) ↝ b
  `β++₁ : ∀ {σ} {xs : Γ ⊢ `list σ} → Γ ⊢ `list σ ∋ `[] `++ xs ↝ xs
  `β++₂ : ∀ {σ hd} {tl xs : Γ ⊢ `list σ} → Γ ⊢ `list σ ∋ (hd `∷ tl) `++ xs ↝ hd `∷ (tl `++ xs)
  `βmap₁ : ∀ {σ τ} {f : Γ ⊢ σ `→ τ} → Γ ⊢ `list τ ∋ `map f `[] ↝ `[]
  `βmap₂ : ∀ {σ τ} {f : Γ ⊢ σ `→ τ} {hd tl} →
          Γ ⊢ `list τ ∋ `map f (hd `∷ tl) ↝ (f `$ hd) `∷ `map f tl
  `βfold₁ : ∀ {σ τ c n} → Γ ⊢ τ ∋ `fold {σ = σ} c n `[] ↝ n
  `βfold₂ : ∀ {σ τ c n hd tl} → Γ ⊢ τ ∋ `fold {σ = σ} c n (hd `∷ tl) ↝ c `$ hd `$ `fold c n tl
-- eta laws
  `ηλ : ∀ {σ τ} f → Γ ⊢ σ `→ τ ∋ f ↝ η-expand f
  `η× : ∀ {σ τ} t → Γ ⊢ σ `× τ ∋ t ↝ `π₁ t `, `π₂ t
  `η1 : ∀ t → Γ ⊢ `1 ∋ t ↝ `⟨⟩
  `ηmap₁ : ∀ {σ} t → Γ ⊢ `list σ ∋ t ↝ `map (`λ (`v here!)) t
  `ηmap₂ : ∀ {σ τ} {f : Γ ⊢ σ `→ τ} xs ys →
           Γ ⊢ `list τ ∋ `map f (xs `++ ys) ↝ `map f xs `++ `map f ys
  `ηmap₃ : ∀ {σ τ υ} (g : Γ ⊢ τ `→ υ) (f : Γ ⊢ σ `→ τ) (xs : Γ ⊢ `list σ) →
           Γ ⊢ `list υ ∋ `map g (`map f xs) ↝ `map (g `∘ f) xs
  `ηfold₁ : ∀ {σ τ c n} xs ys → Γ ⊢ τ ∋ `fold {σ = σ} c n (xs `++ ys) ↝ `fold c (`fold c n ys) xs
  `ηfold₂ : ∀ {σ τ υ n} c f xs →
            Γ ⊢ τ ∋ `fold {σ = σ} c n (`map {σ = υ} f xs) ↝ `fold (c `∘ f) n xs
  `η++₁ : ∀ {σ} t → Γ ⊢ `list σ ∋ t ↝ t `++ `[]
  `η++₂ : ∀ {σ} xs ys zs → Γ ⊢ `list σ ∋ (xs `++ ys) `++ zs ↝ xs `++ (ys `++ zs)

↝-weaken : ∀ {n Γ Δ} {σ : ty n} {s t} (inc : Γ ⊆ Δ) (r : Γ ⊢ σ ∋ s ↝ t) →
            Δ ⊢ σ ∋ ⊢-weaken inc s ↝ ⊢-weaken inc t
↝-weaken inc (`λ r) = `λ (↝-weaken (pop! inc) r)
↝-weaken inc (`$₁ r) = `$₁ (↝-weaken inc r)
↝-weaken inc (`$₂ r) = `$₂ (↝-weaken inc r)
↝-weaken inc (`,₁ r) = `,₁ (↝-weaken inc r)
↝-weaken inc (`,₂ r) = `,₂ (↝-weaken inc r)
↝-weaken inc (`π₁ r) = `π₁ (↝-weaken inc r)
↝-weaken inc (`π₂ r) = `π₂ (↝-weaken inc r)
↝-weaken inc (`∷₁ r) = `∷₁ (↝-weaken inc r)
↝-weaken inc (`∷₂ r) = `∷₂ (↝-weaken inc r)
↝-weaken inc (`++₁ r) = `++₁ (↝-weaken inc r)
↝-weaken inc (`++₂ r) = `++₂ (↝-weaken inc r)
↝-weaken inc (`map₁ r) = `map₁ (↝-weaken inc r)
↝-weaken inc (`map₂ r) = `map₂ (↝-weaken inc r)
↝-weaken inc (`fold₁ r) = `fold₁ (↝-weaken inc r)
↝-weaken inc (`fold₂ r) = `fold₂ (↝-weaken inc r)
↝-weaken inc (`fold₃ r) = `fold₃ (↝-weaken inc r)
↝-weaken inc (`βλ {σ} {τ} {t} {s}) rewrite β-weaken inc t s = `βλ
↝-weaken inc `βπ₁ = `βπ₁
↝-weaken inc `βπ₂ = `βπ₂
↝-weaken inc `β++₁ = `β++₁
↝-weaken inc `β++₂ = `β++₂
↝-weaken inc `βmap₁ = `βmap₁
↝-weaken inc `βmap₂ = `βmap₂
↝-weaken inc `βfold₁ = `βfold₁
↝-weaken inc `βfold₂ = `βfold₂
↝-weaken inc (`ηλ t) rewrite η-weaken inc t = `ηλ (⊢-weaken inc t)
↝-weaken inc (`η× t) = `η× (⊢-weaken inc t)
↝-weaken inc (`η1 t) = `η1 (⊢-weaken inc t)
↝-weaken inc (`ηmap₁ t) = `ηmap₁ (⊢-weaken inc t)
↝-weaken inc (`ηmap₂ xs ys) = `ηmap₂ (⊢-weaken inc xs) (⊢-weaken inc ys)
↝-weaken inc (`ηmap₃ g f xs) rewrite `∘-weaken inc g f =
  `ηmap₃ (⊢-weaken inc g) (⊢-weaken inc f) (⊢-weaken inc xs)
↝-weaken inc (`ηfold₁ xs ys) = `ηfold₁ (⊢-weaken inc xs) (⊢-weaken inc ys)
↝-weaken inc (`ηfold₂ c f xs) rewrite `∘-weaken inc c f =
  `ηfold₂ (⊢-weaken inc c) (⊢-weaken inc f) (⊢-weaken inc xs)
↝-weaken inc (`η++₁ t) = `η++₁ (⊢-weaken inc t)
↝-weaken inc (`η++₂ xs ys zs) = `η++₂ (⊢-weaken inc xs) (⊢-weaken inc ys) (⊢-weaken inc zs)

_⊢_∋_↝⋆_ : ∀ {n} Γ (τ : ty n) (s t : Γ ⊢ τ) → Set
Γ ⊢ σ ∋ s ↝⋆ t = s ▹[ _⊢_∋_↝_ Γ σ ]⋆ t

↝⋆-weaken : ∀ {n Γ Δ} {σ : ty n} {s t} (inc : Γ ⊆ Δ) (r : Γ ⊢ σ ∋ s ↝⋆ t) →
            Δ ⊢ σ ∋ ⊢-weaken inc s ↝⋆ ⊢-weaken inc t
↝⋆-weaken inc r = ▹⋆-cong (↝-weaken inc) r

_⊢_∋_≅_ : ∀ {n} Γ (τ : ty n) (s t : Γ ⊢ τ) → Set
Γ ⊢ σ ∋ s ≅ t = s ≡[ _⊢_∋_↝_ Γ σ ]⋆ t

≅-weaken : ∀ {n Γ Δ} {σ : ty n} {s t} (inc : Γ ⊆ Δ) (r : Γ ⊢ σ ∋ s ≅ t) →
            Δ ⊢ σ ∋ ⊢-weaken inc s ≅ ⊢-weaken inc t
≅-weaken inc r = ≡⋆-cong (↝-weaken inc) r

{- notations for equational reasoning -}

infix  3 _⊢_∋_Qed
infixr 2 _⊢_∋_↝⋆⟨_⟩_ _⊢_∋_↝⟨_⟩_ _⊢_∋_≡⟨_⟩_
infix  1 Proof[_⊢_]_

Proof[_⊢_]_ : ∀ {n} Γ (σ : ty n) {s t : Γ ⊢ σ} (eq : Γ ⊢ σ ∋ s ↝⋆ t) → Γ ⊢ σ ∋ s ↝⋆ t
Proof[ Γ ⊢ σ ] eq = eq

_⊢_∋_≡⟨_⟩_ : ∀ {n} Γ (σ : ty n) s {t u : Γ ⊢ σ} (eq : s ≡ t) (eq' : Γ ⊢ σ ∋ t ↝⋆ u) → Γ ⊢ σ ∋ s ↝⋆ u
Γ ⊢ σ ∋ s ≡⟨ refl ⟩ eq = eq

_⊢_∋_↝⋆⟨_⟩_ : ∀ {n} Γ (σ : ty n) (s : Γ ⊢ σ) {t u : Γ ⊢ σ} (eq : Γ ⊢ σ ∋ s ↝⋆ t)
  (eq' : Γ ⊢ σ ∋ t ↝⋆ u) → Γ ⊢ σ ∋ s ↝⋆ u
Γ ⊢ σ ∋ s ↝⋆⟨ eq ⟩ eq' = ▹⋆-trans eq eq'

_⊢_∋_↝⟨_⟩_ : ∀ {n} Γ (σ : ty n) (s : Γ ⊢ σ) {t u : Γ ⊢ σ} (eq : Γ ⊢ σ ∋ s ↝ t)
  (eq' : Γ ⊢ σ ∋ t ↝⋆ u) → Γ ⊢ σ ∋ s ↝⋆ u
Γ ⊢ σ ∋ s ↝⟨ eq ⟩ eq' = step eq eq'

_⊢_∋_Qed : ∀ {n} Γ (σ : ty n) (s : Γ ⊢ σ) → Γ ⊢ σ ∋ s ↝⋆ s
Γ ⊢ σ ∋ s Qed = refl
