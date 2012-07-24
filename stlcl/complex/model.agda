module stlcl.complex.model where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

open import tools.contexts
open import tools.closures
open import stlcl.definition
open import stlcl.reductions
open import stlcl.normalforms

data _⊩list_[_] (Γ : Con ty) {σ : ty} (Σ : ∀ Δ (t : Δ ⊢ σ) → Set) (t : Γ ⊢ `list σ) : Set where
  `[] : (r : Γ ⊢ `list σ ∋ t ↝⋆ `[]) → Γ ⊩list Σ [ t ]
  _`∷_by_ : ∀ {hd tl} (HD : Σ Γ hd) (TL : Γ ⊩list Σ [ tl ])
         (r : Γ ⊢ `list σ ∋ t ↝⋆ hd `∷ tl) → Γ ⊩list Σ [ t ]
  mappend : ∀ {τ} {f : Γ ⊢ τ `→ σ}
    (F : ∀ {Δ} (inc : Γ ⊆ Δ) (t : Δ ⊢ne τ) → Σ Δ (⊢-weaken inc f `$ (back-ne t)))
    (xs : Γ ⊢ne `list τ) {ys} (YS : Γ ⊩list Σ [ ys ])
    (r : Γ ⊢ `list σ ∋ t ↝⋆ `map f (back-ne xs) `++ ys) → Γ ⊩list Σ [ t ]

_⊩_[_] : ∀ Γ σ (t : Γ ⊢ σ) → Set
Γ ⊩ `1 [ t ] = ⊤
Γ ⊩ σ `× τ [ t ] =
  Σ (Γ ⊢ σ) (λ a →
  Σ (Γ ⊢ τ) (λ b →
  Σ (Γ ⊢ σ `× τ ∋ t ↝⋆ a `, b) (λ r →
  Γ ⊩ σ [ a ] × Γ ⊩ τ [ b ])))
Γ ⊩ σ `→ τ [ t ] =
   ∀ {Δ} (inc : Γ ⊆ Δ) {s} (v : Δ ⊩ σ [ s ])
     {ts} (r : Δ ⊢ τ ∋ ts ↝⋆ ⊢-weaken inc t `$ s) → Δ ⊩ τ [ ts ]
Γ ⊩ `list σ [ t ] = Γ ⊩list (λ Δ t → Δ ⊩ σ [ t ]) [ t ]

⊩-↝⋆ : ∀ σ {Γ s t} (r : Γ ⊢ σ ∋ s ↝⋆ t) (T : Γ ⊩ σ [ t ]) → Γ ⊩ σ [ s ]
⊩-↝⋆ `1 r T = tt
⊩-↝⋆ (σ `× τ) r (a , b , r' , A , B) = a , b , ▹⋆-trans r r' , A , B
⊩-↝⋆ (σ `→ τ) r T = λ inc S r' → T inc S (▹⋆-trans r' (▹⋆-cong `$₁ (↝⋆-weaken inc r)))
⊩-↝⋆ (`list σ) r (`[] r') = `[] (▹⋆-trans r r')
⊩-↝⋆ (`list σ) r (HD `∷ T by r') = HD `∷ T by ▹⋆-trans r r'
⊩-↝⋆ (`list σ) r (mappend F xs T r') = mappend F xs T (▹⋆-trans r r')

⊩-weaken : ∀ σ {Γ Δ} (inc : Γ ⊆ Δ) {t : Γ ⊢ σ} (T : Γ ⊩ σ [ t ]) → Δ ⊩ σ [ ⊢-weaken inc t ]
⊩-weaken `1 inc T = tt
⊩-weaken (σ `× τ) inc (a , b , r , A , B) =
  ⊢-weaken inc a , ⊢-weaken inc b , ↝⋆-weaken inc r , ⊩-weaken σ inc A , ⊩-weaken τ inc B
⊩-weaken (σ `→ τ) inc T =
  λ {Ε} inc' {s} S {ts} r → T (⊆-trans inc inc') S
  (▹⋆-trans r (≡-step (cong (λ t → t `$ s) (⊢-weaken² inc inc' _)) refl))
⊩-weaken (`list σ) inc (`[] r) = `[] (↝⋆-weaken inc r)
⊩-weaken (`list σ) inc (HD `∷ T by r) =
  ⊩-weaken _ inc HD `∷ ⊩-weaken _ inc T by ↝⋆-weaken inc r
⊩-weaken (`list σ) inc (mappend {τ} {f} F xs {ys} T r) =
  mappend
  (λ {Ε} inc' t →
    ⊩-↝⋆ σ (≡-step (cong (λ s → s `$ back-ne t) (⊢-weaken² inc inc' _)) refl)
    (F (⊆-trans inc inc') t))
  (ne-weaken inc xs)
  (⊩-weaken _ inc T) (▹⋆-trans (↝⋆-weaken inc r) (≡-step
  (cong (λ s → `map (⊢-weaken inc f) s `++ ⊢-weaken inc ys) (sym (ne-weaken-back inc xs))) refl))

↑list[_]_ : ∀ {σ Γ t} (Σ : ∀ {Δ t} (T : Δ ⊩ σ [ t ]) → Δ ⊢nf σ)
            (T : Γ ⊩ `list σ [ t ]) → Γ ⊢nf `list σ
↑list[ Σ ] `[] r = `[]
↑list[ Σ ] (HD `∷ T by r) = Σ HD `∷ ↑list[ Σ ] T
↑list[ Σ ] mappend F xs T r = mappend (`λ (Σ (F (step (same _)) (`v here!)))) xs (↑list[ Σ ] T)

list[_]_↝⋆↑_ : ∀ {σ Γ} {Σ : ∀ {Δ t} (T : Δ ⊩ σ [ t ]) → Δ ⊢nf σ}
               (↑Σ : ∀ {Δ t} (T : Δ ⊩ σ [ t ]) → Δ ⊢ σ ∋ t ↝⋆ back-nf (Σ T))
               t (T : Γ ⊩ `list σ [ t ]) → Γ ⊢ `list σ ∋ t ↝⋆ back-nf (↑list[ Σ ] T)
list[ ↑Σ ] t ↝⋆↑ `[] r = r
list[ ↑Σ ] t ↝⋆↑ (HD `∷ T by r) =
  ▹⋆-trans r (▹⋆-trans (▹⋆-cong `∷₁ (↑Σ HD)) (▹⋆-cong `∷₂ (list[ ↑Σ ] _ ↝⋆↑ T)))
list[ ↑Σ ] t ↝⋆↑ mappend {τ} {f} F xs T r =
  ▹⋆-trans r (▹⋆-trans (▹⋆-cong `++₂ (list[ ↑Σ ] _ ↝⋆↑ T))
  (▹⋆-cong {f = λ t → `map t (back-ne xs) `++ back-nf (↑list[ _ ] T)} (λ p → `++₁ (`map₁ p))
  (step (`ηλ f) (▹⋆-cong `λ (↑Σ (F (step (⊆-refl _)) (`v here!)))))))

mutual

  ↑[_]_ : ∀ σ {Γ t} (T : Γ ⊩ σ [ t ]) → Γ ⊢nf σ
  ↑[ `1 ] T = `⟨⟩
  ↑[ σ `× τ ] (a , b , r , A , B) = ↑[ σ ] A `, ↑[ τ ] B
  ↑[ σ `→ τ ] T = `λ (↑[ τ ] T (step (same _)) (↓[ σ ] `v here!) refl)
  ↑[ `list σ ] T = ↑list[ ↑[_]_ σ ] T

  ↓[_]_ : ∀ σ {Γ} (t : Γ ⊢ne σ) → Γ ⊩ σ [ back-ne t ]
  ↓[ `1 ] t = tt
  ↓[ σ `× τ ] t =
    back-ne (`π₁ t) , back-ne (`π₂ t) , step (`η× (back-ne t)) refl ,
    ↓[ σ ] `π₁ t , ↓[ τ ] `π₂ t
  ↓[ σ `→ τ ] t =
    λ {Δ} inc {s} S {ts} r → ⊩-↝⋆ τ (▹⋆-trans r (▹⋆-trans (▹⋆-cong `$₂ ([ σ ] s ↝⋆↑ S))
    (≡-step (cong (λ t → t `$ back-nf (↑[ σ ] S)) (sym (ne-weaken-back inc t))) refl)))
    (↓[ τ ] (ne-weaken inc t `$ ↑[ σ ] S))
  ↓[ `list σ ] t =
     mappend (λ _ t → ⊩-↝⋆ σ (step `βλ refl) (↓[ σ ] t)) t (`[] refl)
     (step (`ηmap₁ (back-ne t)) (step (`η++₁ _) refl))

  [_]_↝⋆↑_ : ∀ σ {Γ} (t : Γ ⊢ σ) (T : Γ ⊩ σ [ t ]) → Γ ⊢ σ ∋ t ↝⋆ back-nf (↑[ σ ] T)
  [ `1 ] t ↝⋆↑ T = step (`η1 t) refl
  [ σ `× τ ] t ↝⋆↑ (a , b , r , A , B) =
    ▹⋆-trans r (▹⋆-trans (▹⋆-cong `,₁ ([ σ ] a ↝⋆↑ A)) (▹⋆-cong `,₂ ([ τ ] b ↝⋆↑ B)))
  [ σ `→ τ ] t ↝⋆↑ T = step (`ηλ t) (▹⋆-cong `λ ([ τ ] _ ↝⋆↑ _))
  [ `list σ ] t ↝⋆↑ T = list[ [_]_↝⋆↑_ σ _ ] t ↝⋆↑ T

_⊩ε_[_] : ∀ (Δ Γ : Con ty) (ρ : Δ ⊢ε Γ) → Set
Δ ⊩ε ε [ ρ ] = ⊤
Δ ⊩ε Γ ∙ σ [ ρ , r ] = Δ ⊩ε Γ [ ρ ] × Δ ⊩ σ [ r ]

⊩ε-weaken : ∀ Γ {Δ Ε} (inc : Δ ⊆ Ε) {ρ} (vs : Δ ⊩ε Γ [ ρ ]) → Ε ⊩ε Γ [ ⊢ε-weaken Γ inc ρ ]
⊩ε-weaken ε inc vs = vs
⊩ε-weaken (Γ ∙ σ) inc (vs , v) = ⊩ε-weaken Γ inc vs , ⊩-weaken σ inc v

⊩ε-refl : (Γ : Con ty) → Γ ⊩ε Γ [ ⊢ε-refl Γ ]
⊩ε-refl ε = tt
⊩ε-refl (Γ ∙ σ) = ⊩ε-weaken Γ (step (same _)) (⊩ε-refl Γ) , ↓[ σ ] `v here!
