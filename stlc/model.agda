module stlc.model where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

open import tools.contexts
open import tools.closures
open import stlc.definition
open import stlc.reductions

infix 10 _⊢ne_ _⊢nf_ _⊩τ_[_] _⊩ε_[_]

{- definition of neutral and normal forms -}

mutual

  data _⊢ne_ (Γ : Con ty) : ty → Set where
    var : ∀ {σ : ty} (pr : σ ∈ Γ) → Γ ⊢ne σ
    app : ∀ {σ τ} (f : Γ ⊢ne σ ▹ τ) (x : Γ ⊢nf σ) → Γ ⊢ne τ

  data _⊢nf_ (Γ : Con ty) : ty → Set where
    neu : ∀ (t : Γ ⊢ne ♭) → Γ ⊢nf ♭
    lam : ∀ {σ τ} (t : Γ ∙ σ ⊢nf τ) → Γ ⊢nf σ ▹ τ

mutual

  back-nf : ∀ {Γ σ} → Γ ⊢nf σ → Γ ⊢ σ
  back-nf (neu t) = back-ne t
  back-nf (lam t) = lam (back-nf t)

  back-ne : ∀ {Γ σ} → Γ ⊢ne σ → Γ ⊢ σ
  back-ne (var pr) = var pr
  back-ne (app f x) = app (back-ne f) (back-nf x)

{- A neutral term is neutral -}

neutrality : ∀ {Γ σ} t → Γ ⊢ne σ ∋ back-ne t
neutrality (var pr) = var pr
neutrality (app f x) = app (neutrality f)

{- weakening -}

mutual

  weaken-nf : ∀ {Γ Δ σ} → Γ ⊆ Δ → Γ ⊢nf σ → Δ ⊢nf σ
  weaken-nf inc (neu t) = neu (weaken-ne inc t)
  weaken-nf inc (lam t) = lam (weaken-nf (pop! inc) t)

  weaken-ne : ∀ {Γ Δ σ} → Γ ⊆ Δ → Γ ⊢ne σ → Δ ⊢ne σ
  weaken-ne inc (var pr) = var (inc-in inc pr)
  weaken-ne inc (app f x) = app (weaken-ne inc f) (weaken-nf inc x)

mutual

  weaken-nf-refl : ∀ {Γ σ} (t : Γ ⊢nf σ) → t ≡ weaken-nf (same _) t
  weaken-nf-refl (neu t) = cong neu (weaken-ne-refl t)
  weaken-nf-refl (lam t) = cong lam (weaken-nf-refl t)

  weaken-ne-refl : ∀ {Γ σ} (t : Γ ⊢ne σ) → t ≡ weaken-ne (same _) t
  weaken-ne-refl (var pr) = cong var (sym (inc-in-same pr))
  weaken-ne-refl (app t x) = cong₂ app (weaken-ne-refl t) (weaken-nf-refl x)

mutual

  weaken-ne² : ∀ {Γ Δ Ε σ} (pr₁ : Γ ⊆ Δ) (pr₂ : Δ ⊆ Ε) (t : Γ ⊢ne σ) →
    weaken-ne pr₂ (weaken-ne pr₁ t) ≡ weaken-ne (⊆-trans pr₁ pr₂) t
  weaken-ne² pr₁ pr₂ (var pr) = cong var (inc-in² pr₁ pr₂ pr)
  weaken-ne² pr₁ pr₂ (app t x) = cong₂ app (weaken-ne² pr₁ pr₂ t) (weaken-nf² pr₁ pr₂ x)

  weaken-nf² : ∀ {Γ Δ Ε σ} (pr₁ : Γ ⊆ Δ) (pr₂ : Δ ⊆ Ε) (t : Γ ⊢nf σ) →
    weaken-nf pr₂ (weaken-nf pr₁ t) ≡ weaken-nf (⊆-trans pr₁ pr₂) t
  weaken-nf² pr₁ pr₂ (neu t) = cong neu (weaken-ne² pr₁ pr₂ t)
  weaken-nf² pr₁ pr₂ (lam t) = cong lam (weaken-nf² (pop! pr₁) (pop! pr₂) t)

{- definition of the target model for the normalization by evaluation -}

_⊩τ_[_] : (Γ : Con ty) (τ : ty) → Γ ⊢ τ → Set
Γ ⊩τ ♭ [ t ] = Σ (Γ ⊢ne ♭) (λ u → t ▹⋆ back-ne u)
Γ ⊩τ σ ▹ τ [ f ] = ∀ {Δ : Con ty} {s : Δ ⊢ σ} (pr : Γ ⊆ Δ) →
                   Δ ⊩τ σ [ s ] → Δ ⊩τ τ [ app (weaken pr f) s ]

_⊩ε_[_] : (Δ Γ : Con ty) → Δ ⊩ Γ → Set
Δ ⊩ε ε [ _ ] = ⊤
Δ ⊩ε (Γ ∙ σ) [ r , ρ ] = Δ ⊩τ σ [ r ] × Δ ⊩ε Γ [ ρ ]

mutual

  back-weaken-nf : ∀ {Γ Δ σ} (pr : Γ ⊆ Δ) (t : Γ ⊢nf σ) →
                   back-nf (weaken-nf pr t) ≡ weaken pr (back-nf t)
  back-weaken-nf pr (neu t) = back-weaken-ne pr t
  back-weaken-nf pr (lam t) = cong lam (back-weaken-nf (pop! pr) t)

  back-weaken-ne : ∀ {Γ Δ σ} (pr : Γ ⊆ Δ) (t : Γ ⊢ne σ) →
                   back-ne (weaken-ne pr t) ≡ weaken pr (back-ne t)
  back-weaken-ne pr (var pr') = refl
  back-weaken-ne pr (app f x) = cong₂ app (back-weaken-ne pr f) (back-weaken-nf pr x)

{- weakening of evaluation contexts -}

⊩τ-weaken : ∀ {σ} {Γ Δ : Con ty} s (pr : Γ ⊆ Δ) → Γ ⊩τ σ [ s ] → Δ ⊩τ σ [ weaken pr s ]
⊩τ-weaken {♭} s Hin (t , Ht) = weaken-ne Hin t ,
  coerce (λ t → weaken Hin s ▹⋆ t) (sym (back-weaken-ne Hin t)) (▹⋆-cong (▹-weaken Hin) Ht)
⊩τ-weaken {σ ▹ τ} {Γ} {Δ} g Hin f =
  λ {Ε} {x} pr s → coerce (λ t → Ε ⊩τ τ [ app t x ]) (sym (weaken² Hin pr g)) (f _ s)

⊩ε-weaken : ∀ (Γ : Con ty) {Δ Ε} {ρ : Δ ⊩ Γ} (pr : Δ ⊆ Ε) →
             Δ ⊩ε Γ [ ρ ] → Ε ⊩ε Γ [ ⊩-weaken Γ pr ρ ]
⊩ε-weaken ε pr vs = vs
⊩ε-weaken (Γ ∙ _) {Δ} {Ε} {r , ρ} pr (v , vs) = ⊩τ-weaken r pr v , ⊩ε-weaken Γ pr vs

ne-weaken : ∀ {Γ σ t Δ} (inc : Γ ⊆ Δ) (ne : Γ ⊢ne σ ∋ t) → Δ ⊢ne σ ∋ weaken inc t
ne-weaken inc (var pr) = var (inc-in inc pr)
ne-weaken inc (app ne) = app (ne-weaken inc ne)

{-------------------------------------------------}
{------- Let's go back to the computations -------}
{-------------------------------------------------}

{- the model is closed under ▹⋆-expansion -}

⊩τ-◃ : ∀ {τ Γ s t} (r : Γ ⊢ τ ∋ s ▹ t) → Γ ⊩τ τ [ t ] → Γ ⊩τ τ [ s ]
⊩τ-◃ {♭} r (v , Hv) = v , step r Hv
⊩τ-◃ {σ ▹ τ} r f = λ {Δ} {s} pr v → ⊩τ-◃ {τ} (apl (▹-weaken pr r)) (f pr v)

⊩τ-⋆◃ : ∀ {τ Γ s t} (r : s ▹⋆ t) → Γ ⊩τ τ [ t ] → Γ ⊩τ τ [ s ]
⊩τ-⋆◃ refl v = v
⊩τ-⋆◃ (step p r) v = ⊩τ-◃ p (⊩τ-⋆◃ r v)

{- quoting -}

mutual

  ↑ : ∀ {σ Γ} {t : Γ ⊢ σ} → Γ ⊩τ σ [ t ] → Γ ⊢nf σ
  ↑ {♭} (t , _) = neu t
  ↑ {σ ▹ τ} {Γ} f = lam (↑ (f (step (same Γ)) (↓ {σ} (var here!))))

  ↓ : ∀ {σ Γ} (t : Γ ⊢ne σ) → Γ ⊩τ σ [ back-ne t ]
  ↓ {♭} t = t , refl
  ↓ {σ ▹ τ} f = λ {Δ} {s} inc v →
  {- administrative business: the model is cclosed under reductions -}
    ⊩τ-⋆◃ {τ} {Δ} (coerce (λ t → app (weaken inc (back-ne f)) s ▹⋆ app t (back-nf (↑ v)))
    (sym (back-weaken-ne inc f)) (▹⋆-cong apr (↑▹⋆ σ s v)))
  {- actual computation -}
    (↓ {τ} (app (weaken-ne inc f) (↑ {σ} v)))

  ↑▹⋆ : ∀ σ {Γ} (t : Γ ⊢ σ) (v : Γ ⊩τ σ [ t ]) → t ▹⋆ back-nf (↑ v)
  ↑▹⋆ ♭ t (v , Hv) = Hv
  ↑▹⋆ (σ ▹ τ) t vf =
    step eta (▹⋆-cong lam (↑▹⋆ τ (app (weaken (step (same _)) t) _) (vf _ (↓ {σ} _))))
