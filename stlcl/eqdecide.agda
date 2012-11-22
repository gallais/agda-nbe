module stlcl.eqdecide where

open import tools.contexts
open import tools.closures

open import stlcl.definition
open import stlcl.reductions
open import stlcl.simple.eval
open import stlcl.simple.sound
open import stlcl.simple.complete

open import Data.Fin
open import Data.Product
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

suc-inv : ∀ {n} {k₁ k₂ : Fin n} (eq : suc k₁ ≡ suc k₂) → k₁ ≡ k₂
suc-inv refl = refl

Fin-dec : ∀ {n} (k₁ k₂ : Fin n) → Dec (k₁ ≡ k₂)
Fin-dec zero zero = yes refl
Fin-dec zero (suc k₂) = no (λ ())
Fin-dec (suc k₁) zero = no (λ ())
Fin-dec (suc k₁) (suc k₂) with Fin-dec k₁ k₂
... | yes p rewrite p = yes refl
... | no ¬p = no (λ p → ¬p (suc-inv p))

-- decidability of equality between types

`b-inv : ∀ {n} {k₁ k₂ : Fin n} (eq : `b k₁ ≡ `b k₂) → k₁ ≡ k₂
`b-inv refl = refl

`×-inv : ∀ {n} {σ₁ σ₂ τ₁ τ₂ : ty n} (eq : σ₁ `× τ₁ ≡ σ₂ `× τ₂) → (σ₁ ≡ σ₂) × (τ₁ ≡ τ₂)
`×-inv refl = refl , refl

`→-inv : ∀ {n} {σ₁ σ₂ τ₁ τ₂ : ty n} (eq : σ₁ `→ τ₁ ≡ σ₂ `→ τ₂) → (σ₁ ≡ σ₂) × (τ₁ ≡ τ₂)
`→-inv refl = refl , refl

`list-inv : ∀ {n} {σ₁ σ₂ : ty n} (eq : `list σ₁ ≡ `list σ₂) → σ₁ ≡ σ₂
`list-inv refl = refl

ty-dec : ∀ {n} (σ τ : ty n) → Dec (σ ≡ τ)
ty-dec `1 `1 = yes refl
ty-dec (`b k₁) (`b k₂) with Fin-dec k₁ k₂
... | yes p rewrite p = yes refl
... | no ¬p = no (λ p → ¬p (`b-inv p))
ty-dec (σ₁ `× τ₁) (σ₂ `× τ₂) with ty-dec σ₁ σ₂ | ty-dec τ₁ τ₂
... | yes p₁ | yes p₂ = yes (cong₂ _`×_ p₁ p₂)
... | no ¬p₁ | _ = no (λ p → ¬p₁ (proj₁ (`×-inv p)))
... | _ | no ¬p₂ = no (λ p → ¬p₂ (proj₂ (`×-inv p)))
ty-dec (σ₁ `→ τ₁) (σ₂ `→ τ₂) with ty-dec σ₁ σ₂ | ty-dec τ₁ τ₂
... | yes p₁ | yes p₂ = yes (cong₂ _`→_ p₁ p₂)
... | no ¬p₁ | _ = no (λ p → ¬p₁ (proj₁ (`→-inv p)))
... | _ | no ¬p₂ = no (λ p → ¬p₂ (proj₂ (`→-inv p)))
ty-dec (`list σ₁) (`list σ₂) with ty-dec σ₁ σ₂
... | yes p = yes (cong `list_ p)
... | no ¬p = no (λ p → ¬p (`list-inv p))
ty-dec `1 (`b _) = no (λ ())
ty-dec `1 (_ `× _) = no (λ ())
ty-dec `1 (_ `→ _) = no (λ ())
ty-dec `1 (`list _) = no (λ ())
ty-dec (`b _) `1 = no (λ ())
ty-dec (`b _) (_ `× _) = no (λ ())
ty-dec (`b _) (_ `→ _) = no (λ ())
ty-dec (`b _) (`list _) = no (λ ())
ty-dec (_ `× _) `1 = no (λ ())
ty-dec (_ `× _) (`b _) = no (λ ())
ty-dec (_ `× _) (_ `→ _) = no (λ ())
ty-dec (_ `× _) (`list _) = no (λ ())
ty-dec (_ `→ _) `1 = no (λ ())
ty-dec (_ `→ _) (`b _) = no (λ ())
ty-dec (_ `→ _) (_ `× _) = no (λ ())
ty-dec (_ `→ _) (`list _) = no (λ ())
ty-dec (`list _) `1 = no (λ ())
ty-dec (`list _) (`b _) = no (λ ())
ty-dec (`list _) (_ `× _) = no (λ ())
ty-dec (`list _) (_ `→ _) = no (λ ())

-- decidability of equality of terms

`v-inv : ∀ {n Γ} {σ : ty n} {pr₁ pr₂ : σ ∈ Γ} (eq : _≡_ {A = Γ ⊢ σ} (`v pr₁) (`v pr₂)) → pr₁ ≡ pr₂
`v-inv refl = refl

`λ-inv : ∀ {n Γ} {σ τ : ty n} {t₁ t₂ : Γ ∙ σ ⊢ τ}
  (eq : _≡_ {A = Γ ⊢ σ `→ τ} (`λ t₁) (`λ t₂)) → t₁ ≡ t₂
`λ-inv refl = refl

`$-ty-inv : ∀ {n Γ} {σ₁ σ₂ τ : ty n} {t₁ : Γ ⊢ σ₁ `→ τ} {t₂ : Γ ⊢ σ₂ `→ τ} {u₁ : Γ ⊢ σ₁} {u₂ : Γ ⊢ σ₂}
  (eq : _≡_ {A = Γ ⊢ τ} (t₁ `$ u₁) (t₂ `$ u₂)) → σ₁ ≡ σ₂
`$-ty-inv refl = refl

`$-inv : ∀ {n Γ} {σ τ : ty n} {t₁ t₂ : Γ ⊢ σ `→ τ} {u₁ u₂ : Γ ⊢ σ}
  (eq : _≡_ {A = Γ ⊢ τ} (t₁ `$ u₁) (t₂ `$ u₂)) → (t₁ ≡ t₂) × (u₁ ≡ u₂)
`$-inv refl = refl , refl

`,-inv : ∀ {n Γ} {σ τ : ty n} {a₁ a₂ : Γ ⊢ σ} {b₁ b₂ : Γ ⊢ τ}
  (eq : _≡_ {A = Γ ⊢ σ `× τ} (a₁ `, b₁) (a₂ `, b₂)) → (a₁ ≡ a₂) × (b₁ ≡ b₂)
`,-inv refl = refl , refl

`π₁-ty-inv : ∀ {n Γ} {σ τ₁ τ₂ : ty n} {t₁ : Γ ⊢ σ `× τ₁} {t₂ : Γ ⊢ σ `× τ₂}
  (eq : _≡_ {A = Γ ⊢ σ} (`π₁ t₁) (`π₁ t₂)) → τ₁ ≡ τ₂
`π₁-ty-inv refl = refl

`π₁-inv : ∀ {n Γ} {σ τ : ty n} {t₁ t₂ : Γ ⊢ σ `× τ} (eq : _≡_ {A = Γ ⊢ σ} (`π₁ t₁) (`π₁ t₂)) → t₁ ≡ t₂
`π₁-inv refl = refl

`π₂-ty-inv : ∀ {n Γ} {σ₁ σ₂ τ : ty n} {t₁ : Γ ⊢ σ₁ `× τ} {t₂ : Γ ⊢ σ₂ `× τ}
  (eq : _≡_ {A = Γ ⊢ τ} (`π₂ t₁) (`π₂ t₂)) → σ₁ ≡ σ₂
`π₂-ty-inv refl = refl

`π₂-inv : ∀ {n Γ} {σ τ : ty n} {t₁ t₂ : Γ ⊢ σ `× τ} (eq : _≡_ {A = Γ ⊢ τ} (`π₂ t₁) (`π₂ t₂)) → t₁ ≡ t₂
`π₂-inv refl = refl

`∷-inv : ∀ {n Γ} {σ : ty n} {hd₁ hd₂ : Γ ⊢ σ} {tl₁ tl₂ : Γ ⊢ `list σ}
  (eq : _≡_ {A = Γ ⊢ `list σ} (hd₁ `∷ tl₁) (hd₂ `∷ tl₂)) → (hd₁ ≡ hd₂) × (tl₁ ≡ tl₂)
`∷-inv refl = refl , refl

`++-inv : ∀ {n Γ} {σ : ty n} {xs₁ xs₂ ys₁ ys₂ : Γ ⊢ `list σ}
  (eq : _≡_ {A = Γ ⊢ `list σ} (xs₁ `++ ys₁) (xs₂ `++ ys₂)) → (xs₁ ≡ xs₂) × (ys₁ ≡ ys₂)
`++-inv refl = refl , refl

`map-ty-inv : ∀ {n Γ} {σ₁ σ₂ τ : ty n} {f₁ : Γ ⊢ σ₁ `→ τ} {f₂ : Γ ⊢ σ₂ `→ τ}
  {xs₁ : Γ ⊢ `list σ₁} {xs₂ : Γ ⊢ `list σ₂}
  (eq : _≡_ {A = Γ ⊢ `list τ} (`map f₁ xs₁) (`map f₂ xs₂)) → σ₁ ≡ σ₂
`map-ty-inv refl = refl

`map-inv : ∀ {n Γ} {σ τ : ty n} {f₁ f₂ : Γ ⊢ σ `→ τ} {xs₁ xs₂ : Γ ⊢ `list σ}
  (eq : _≡_ {A = Γ ⊢ `list τ} (`map f₁ xs₁) (`map f₂ xs₂)) → (f₁ ≡ f₂) × (xs₁ ≡ xs₂)
`map-inv refl = refl , refl

`fold-ty-inv : ∀ {n Γ} {σ₁ σ₂ τ : ty n} {c₁ : Γ ⊢ σ₁ `→ τ `→ τ} {n₁ : Γ ⊢ τ} {xs₁ : Γ ⊢ `list σ₁}
  {c₂ : Γ ⊢ σ₂ `→ τ `→ τ} {n₂ : Γ ⊢ τ} {xs₂ : Γ ⊢ `list σ₂}
  (eq : _≡_ {A = Γ ⊢ τ} (`fold c₁ n₁ xs₁) (`fold c₂ n₂ xs₂)) → σ₁ ≡ σ₂
`fold-ty-inv refl = refl

`fold-inv : ∀ {n Γ} {σ τ : ty n} {c₁ c₂ : Γ ⊢ σ `→ τ `→ τ} {n₁ n₂ : Γ ⊢ τ} {xs₁ xs₂ : Γ ⊢ `list σ}
  (eq : _≡_ {A = Γ ⊢ τ} (`fold c₁ n₁ xs₁) (`fold c₂ n₂ xs₂)) → (c₁ ≡ c₂) × (n₁ ≡ n₂) × (xs₁ ≡ xs₂)
`fold-inv refl = refl , refl , refl

⊢-dec : ∀ {n Γ} {σ : ty n} (s t : Γ ⊢ σ) → Dec (s ≡ t)
⊢-dec (`v pr₁) (`v pr₂) with ∈-dec pr₁ pr₂
... | yes p = yes (cong `v p)
... | no ¬p = no (λ p → ¬p (`v-inv p))
⊢-dec (`λ t₁) (`λ t₂) with ⊢-dec t₁ t₂
... | yes p = yes (cong `λ p)
... | no ¬p = no (λ p → ¬p (`λ-inv p))
⊢-dec (_`$_ {σ₁} t₁ u₁) (_`$_ {σ₂} t₂ u₂) with ty-dec σ₁ σ₂
... | no ¬p = no (λ p → ¬p (`$-ty-inv p))
⊢-dec (t₁ `$ u₁) (t₂ `$ u₂) | yes refl with ⊢-dec t₁ t₂ | ⊢-dec u₁ u₂
... | yes p₁ | yes p₂ = yes (cong₂ _`$_ p₁ p₂)
... | no ¬p₁ | _ = no (λ p → ¬p₁ (proj₁ (`$-inv p)))
... | _ | no ¬p₂ = no (λ p → ¬p₂ (proj₂ (`$-inv p)))
⊢-dec `⟨⟩ `⟨⟩ = yes refl
⊢-dec (a₁ `, b₁) (a₂ `, b₂) with ⊢-dec a₁ a₂ | ⊢-dec b₁ b₂
... | yes p₁ | yes p₂ = yes (cong₂ _`,_ p₁ p₂)
... | no ¬p₁ | _ = no (λ p → ¬p₁ (proj₁ (`,-inv p)))
... | _ | no ¬p₂ = no (λ p → ¬p₂ (proj₂ (`,-inv p)))
⊢-dec (`π₁ {τ = τ₁} p₁) (`π₁ {τ = τ₂} p₂) with ty-dec τ₁ τ₂
... | no ¬p = no (λ p → ¬p (`π₁-ty-inv p))
⊢-dec (`π₁ p₁) (`π₁ p₂) | yes refl with ⊢-dec p₁ p₂
... | yes p = yes (cong `π₁ p)
... | no ¬p = no (λ p → ¬p (`π₁-inv p))
⊢-dec (`π₂ {σ₁} p₁) (`π₂ {σ₂} p₂) with ty-dec σ₁ σ₂
... | no ¬p = no (λ p → ¬p (`π₂-ty-inv p))
⊢-dec (`π₂ p₁) (`π₂ p₂) | yes refl with ⊢-dec p₁ p₂
... | yes p = yes (cong `π₂ p)
... | no ¬p = no (λ p → ¬p (`π₂-inv p))
⊢-dec `[] `[] = yes refl
⊢-dec (hd₁ `∷ tl₁) (hd₂ `∷ tl₂) with ⊢-dec hd₁ hd₂ | ⊢-dec tl₁ tl₂
... | yes p₁ | yes p₂ = yes (cong₂ _`∷_ p₁ p₂)
... | no ¬p₁ | _ = no (λ p → ¬p₁ (proj₁ (`∷-inv p)))
... | _ | no ¬p₂ = no (λ p → ¬p₂ (proj₂ (`∷-inv p)))
⊢-dec (xs₁ `++ ys₁) (xs₂ `++ ys₂) with ⊢-dec xs₁ xs₂ | ⊢-dec ys₁ ys₂
... | yes p₁ | yes p₂ = yes (cong₂ _`++_ p₁ p₂)
... | no ¬p₁ | _ = no (λ p → ¬p₁ (proj₁ (`++-inv p)))
... | _ | no ¬p₂ = no (λ p → ¬p₂ (proj₂ (`++-inv p)))
⊢-dec (`map {τ₁} f₁ xs₁) (`map {τ₂} f₂ xs₂) with ty-dec τ₁ τ₂
... | no ¬p = no (λ p → ¬p (`map-ty-inv p))
⊢-dec (`map f₁ xs₁) (`map f₂ xs₂) | yes refl with ⊢-dec f₁ f₂ | ⊢-dec xs₁ xs₂
... | yes p₁ | yes p₂ = yes (cong₂ `map p₁ p₂)
... | no ¬p₁ | _ = no (λ p → ¬p₁ (proj₁ (`map-inv p)))
... | _ | no ¬p₂ = no (λ p → ¬p₂ (proj₂ (`map-inv p)))
⊢-dec (`fold {σ₁} c₁ n₁ xs₁) (`fold {σ₂} c₂ n₂ xs₂) with ty-dec σ₁ σ₂
... | no ¬p = no (λ p → ¬p (`fold-ty-inv p))
⊢-dec (`fold c₁ n₁ xs₁) (`fold c₂ n₂ xs₂) | yes refl with ⊢-dec c₁ c₂ | ⊢-dec n₁ n₂ | ⊢-dec xs₁ xs₂
... | yes p₁ | yes p₂ | yes p₃ = yes (cong₃ `fold p₁ p₂ p₃)
... | no ¬p₁ | _ | _ = no (λ p → ¬p₁ (proj₁ (`fold-inv p)))
... | _ | no ¬p₂ | _ = no (λ p → ¬p₂ (proj₁ (proj₂ (`fold-inv p))))
... | _ | _ | no ¬p₃ = no (λ p → ¬p₃ (proj₂ (proj₂ (`fold-inv p))))
⊢-dec (`v _) (`λ _) = no (λ ())
⊢-dec (`v _) (_ `$ _) = no (λ ())
⊢-dec (`v _) `⟨⟩ = no (λ ())
⊢-dec (`v _) (_ `, _) = no (λ ())
⊢-dec (`v _) (`π₁ _) = no (λ ())
⊢-dec (`v _) (`π₂ _) = no (λ ())
⊢-dec (`v _) `[] = no (λ ())
⊢-dec (`v _) (_ `∷ _) = no (λ ())
⊢-dec (`v _) (_ `++ _) = no (λ ())
⊢-dec (`v _) (`map _ _) = no (λ ())
⊢-dec (`v _) (`fold _ _ _) = no (λ ())
⊢-dec (`λ _) (`v _) = no (λ ())
⊢-dec (`λ _) (_ `$ _) = no (λ ())
⊢-dec (`λ _) (`π₁ _) = no (λ ())
⊢-dec (`λ _) (`π₂ _) = no (λ ())
⊢-dec (`λ _) (`fold _ _ _) = no (λ ())
⊢-dec (_ `$ _) (`v _) = no (λ ())
⊢-dec (_ `$ _) (`λ _) = no (λ ())
⊢-dec (_ `$ _) `⟨⟩ = no (λ ())
⊢-dec (_ `$ _) (_ `, _) = no (λ ())
⊢-dec (_ `$ _) (`π₁ _) = no (λ ())
⊢-dec (_ `$ _) (`π₂ _) = no (λ ())
⊢-dec (_ `$ _) `[] = no (λ ())
⊢-dec (_ `$ _) (_ `∷ _) = no (λ ())
⊢-dec (_ `$ _) (_ `++ _) = no (λ ())
⊢-dec (_ `$ _) (`map _ _) = no (λ ())
⊢-dec (_ `$ _) (`fold _ _ _) = no (λ ())
⊢-dec `⟨⟩ (`v _) = no (λ ())
⊢-dec `⟨⟩ (_ `$ _) = no (λ ())
⊢-dec `⟨⟩ (`π₁ _) = no (λ ())
⊢-dec `⟨⟩ (`π₂ _) = no (λ ())
⊢-dec `⟨⟩ (`fold _ _ _) = no (λ ())
⊢-dec (_ `, _) (`v _) = no (λ ())
⊢-dec (_ `, _) (_ `$ _) = no (λ ())
⊢-dec (_ `, _) (`π₁ _) = no (λ ())
⊢-dec (_ `, _) (`π₂ _) = no (λ ())
⊢-dec (_ `, _) (`fold _ _ _) = no (λ ())
⊢-dec (`π₁ _) (`v _) = no (λ ())
⊢-dec (`π₁ _) (`λ _) = no (λ ())
⊢-dec (`π₁ _) (_ `$ _) = no (λ ())
⊢-dec (`π₁ _) `⟨⟩ = no (λ ())
⊢-dec (`π₁ _) (_ `, _) = no (λ ())
⊢-dec (`π₁ _) (`π₂ _) = no (λ ())
⊢-dec (`π₁ _) `[] = no (λ ())
⊢-dec (`π₁ _) (_ `∷ _) = no (λ ())
⊢-dec (`π₁ _) (_ `++ _) = no (λ ())
⊢-dec (`π₁ _) (`map _ _) = no (λ ())
⊢-dec (`π₁ _) (`fold _ _ _) = no (λ ())
⊢-dec (`π₂ _) (`v _) = no (λ ())
⊢-dec (`π₂ _) (`λ _) = no (λ ())
⊢-dec (`π₂ _) (_ `$ _) = no (λ ())
⊢-dec (`π₂ _) `⟨⟩ = no (λ ())
⊢-dec (`π₂ _) (_ `, _) = no (λ ())
⊢-dec (`π₂ _) (`π₁ _) = no (λ ())
⊢-dec (`π₂ _) `[] = no (λ ())
⊢-dec (`π₂ _) (_ `∷ _) = no (λ ())
⊢-dec (`π₂ _) (_ `++ _) = no (λ ())
⊢-dec (`π₂ _) (`map _ _) = no (λ ())
⊢-dec (`π₂ _) (`fold _ _ _) = no (λ ())
⊢-dec `[] (`v _) = no (λ ())
⊢-dec `[] (_ `$ _) = no (λ ())
⊢-dec `[] (`π₁ _) = no (λ ())
⊢-dec `[] (`π₂ _) = no (λ ())
⊢-dec `[] (_ `∷ _) = no (λ ())
⊢-dec `[] (_ `++ _) = no (λ ())
⊢-dec `[] (`map _ _) = no (λ ())
⊢-dec `[] (`fold _ _ _) = no (λ ())
⊢-dec (_ `∷ _) (`v _) = no (λ ())
⊢-dec (_ `∷ _) (_ `$ _) = no (λ ())
⊢-dec (_ `∷ _) (`π₁ _) = no (λ ())
⊢-dec (_ `∷ _) (`π₂ _) = no (λ ())
⊢-dec (_ `∷ _) `[] = no (λ ())
⊢-dec (_ `∷ _) (_ `++ _) = no (λ ())
⊢-dec (_ `∷ _) (`map _ _) = no (λ ())
⊢-dec (_ `∷ _) (`fold _ _ _) = no (λ ())
⊢-dec (_ `++ _) (`v _) = no (λ ())
⊢-dec (_ `++ _) (_ `$ _) = no (λ ())
⊢-dec (_ `++ _) (`π₁ _) = no (λ ())
⊢-dec (_ `++ _) (`π₂ _) = no (λ ())
⊢-dec (_ `++ _) `[] = no (λ ())
⊢-dec (_ `++ _) (_ `∷ _) = no (λ ())
⊢-dec (_ `++ _) (`map _ _) = no (λ ())
⊢-dec (_ `++ _) (`fold _ _ _) = no (λ ())
⊢-dec (`map _ _) (`v _) = no (λ ())
⊢-dec (`map _ _) (_ `$ _) = no (λ ())
⊢-dec (`map _ _) (`π₁ _) = no (λ ())
⊢-dec (`map _ _) (`π₂ _) = no (λ ())
⊢-dec (`map _ _) `[] = no (λ ())
⊢-dec (`map _ _) (_ `∷ _) = no (λ ())
⊢-dec (`map _ _) (_ `++ _) = no (λ ())
⊢-dec (`map _ _) (`fold _ _ _) = no (λ ())
⊢-dec (`fold _ _ _) (`v _) = no (λ ())
⊢-dec (`fold _ _ _) (`λ _) = no (λ ())
⊢-dec (`fold _ _ _) (_ `$ _) = no (λ ())
⊢-dec (`fold _ _ _) `⟨⟩ = no (λ ())
⊢-dec (`fold _ _ _) (_ `, _) = no (λ ())
⊢-dec (`fold _ _ _) (`π₁ _) = no (λ ())
⊢-dec (`fold _ _ _) (`π₂ _) = no (λ ())
⊢-dec (`fold _ _ _) `[] = no (λ ())
⊢-dec (`fold _ _ _) (_ `∷ _) = no (λ ())
⊢-dec (`fold _ _ _) (_ `++ _) = no (λ ())
⊢-dec (`fold _ _ _) (`map _ _) = no (λ ())

≅-dec : ∀ {n Γ} {σ : ty n} (s t : Γ ⊢ σ) → Dec (Γ ⊢ σ ∋ s ≅ t)
≅-dec s t with ⊢-dec (norm s) (norm t)
... | yes p = yes (soundness p)
... | no ¬p = no (λ p → ¬p (completeness p))