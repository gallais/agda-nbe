module tools.contexts where

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

{- definition of a context and context inclusion -}

infixl 30 _∙_
data Con (A : Set) : Set where
  ε : Con A
  _∙_ : (Γ : Con A) (σ : A) → Con A

data _⊆_ {A : Set} : Con A → Con A → Set where
  base : ε ⊆ ε
  step : ∀ {Γ : Con A} {Δ : Con A} {σ} (inc : Γ ⊆ Δ) → Γ ⊆ (Δ ∙ σ)
  pop! : ∀ {Γ : Con A} {Δ : Con A} {σ} (inc : Γ ⊆ Δ) → (Γ ∙ σ) ⊆ (Δ ∙ σ)

{- properties of inclusion -}

⊆-refl : ∀ {A : Set} (Γ : Con A) → Γ ⊆ Γ
⊆-refl ε = base
⊆-refl (Γ ∙ _) = pop! (⊆-refl Γ)

syntax ⊆-refl Γ = same Γ

⊆-trans : ∀ {A : Set} {Γ Δ Ε : Con A} → Γ ⊆ Δ → Δ ⊆ Ε → Γ ⊆ Ε
⊆-trans base pr₂ = pr₂
⊆-trans (pop! pr₁) (step pr₂) = step (⊆-trans (pop! pr₁) pr₂)
⊆-trans (pop! pr₁) (pop! pr₂) = pop! (⊆-trans pr₁ pr₂)
⊆-trans (step pr₁) (step pr₂) = step (⊆-trans (step pr₁) pr₂)
⊆-trans (step pr₁) (pop! pr₂) = step (⊆-trans pr₁ pr₂)

abstract

  ⊆-same-l : ∀ {A : Set} {Γ Δ : Con A} (pr : Γ ⊆ Δ) → ⊆-trans (same Γ) pr ≡ pr
  ⊆-same-l base = refl
  ⊆-same-l {A} {ε} (step inc) = refl
  ⊆-same-l {A} {_ ∙ _} (step inc) = cong step (⊆-same-l inc)
  ⊆-same-l (pop! inc) = cong pop! (⊆-same-l inc)

  ⊆-same-r : ∀ {A : Set} {Γ Δ : Con A} (pr : Γ ⊆ Δ) → ⊆-trans pr (same Δ) ≡ pr
  ⊆-same-r base = refl
  ⊆-same-r (step inc) = cong step (⊆-same-r inc)
  ⊆-same-r (pop! inc) = cong pop! (⊆-same-r inc)

  ⊆-same-swap : ∀ {A : Set} {Γ Δ : Con A} (pr : Γ ⊆ Δ) → ⊆-trans pr (same Δ) ≡ ⊆-trans (same Γ) pr
  ⊆-same-swap pr = trans (⊆-same-r pr) (sym (⊆-same-l pr))

  ⊆-step-l : ∀ {A : Set} {Γ Δ Ε} {σ : A} (pr₁ : Γ ⊆ Δ) (pr₂ : Δ ⊆ Ε) →
             step {A} {Γ} {Ε} {σ} (⊆-trans pr₁ pr₂) ≡ ⊆-trans (step pr₁) (pop! pr₂)
  ⊆-step-l base pr₂ = refl
  ⊆-step-l (step pr₁) pr₂ = refl
  ⊆-step-l (pop! pr₁) pr₂ = refl

  ⊆-step-r : ∀ {A : Set} {Γ Δ Ε} {σ : A} (pr₁ : Γ ⊆ Δ) (pr₂ : Δ ⊆ Ε) →
             step {A} {Γ} {Ε} {σ} (⊆-trans pr₁ pr₂) ≡ ⊆-trans pr₁ (step pr₂)
  ⊆-step-r base pr₂ = refl
  ⊆-step-r (step pr₁) pr₂ = refl
  ⊆-step-r (pop! pr₁) pr₂ = refl

  ⊆-step-same : ∀ {A : Set} {Γ Δ} {σ : A} (pr : Γ ⊆ Δ) →
                step {A} {Γ} {Δ} {σ} (⊆-trans (same Γ) pr) ≡ ⊆-trans pr (step (same Δ))
  ⊆-step-same pr = trans (cong step (sym (⊆-same-swap pr))) (⊆-step-r pr (same _))

  ⊆-step₂-same : ∀ {A : Set}  {Γ Δ} {σ τ : A} (pr : Γ ⊆ Δ) →
                 step {A} {Γ} {Δ ∙ σ} {τ} (step (⊆-trans (same Γ) pr))
                 ≡ ⊆-trans pr (step (step (same Δ)))
  ⊆-step₂-same pr = trans (cong step (⊆-step-same pr)) (⊆-step-r pr (step (same _)))

  ⊆-assoc : ∀ {A : Set} {Γ Δ Ε Φ : Con A} (pr₁ : Γ ⊆ Δ) (pr₂ : Δ ⊆ Ε) (pr₃ : Ε ⊆ Φ) →
    ⊆-trans pr₁ (⊆-trans pr₂ pr₃) ≡ ⊆-trans (⊆-trans pr₁ pr₂) pr₃
  ⊆-assoc base pr₂ pr₃ = refl
  ⊆-assoc (step pr₁) (step pr₂) (step pr₃) = cong step (⊆-assoc (step pr₁) (step pr₂) pr₃)
  ⊆-assoc (step pr₁) (step pr₂) (pop! pr₃) = cong step (⊆-assoc (step pr₁) pr₂ pr₃)
  ⊆-assoc (step pr₁) (pop! pr₂) (step pr₃) = cong step (⊆-assoc (step pr₁) (pop! pr₂) pr₃)
  ⊆-assoc (step pr₁) (pop! pr₂) (pop! pr₃) = cong step (⊆-assoc pr₁ pr₂ pr₃)
  ⊆-assoc (pop! pr₁) (step pr₂) (step pr₃) = cong step (⊆-assoc (pop! pr₁) (step pr₂) pr₃)
  ⊆-assoc (pop! pr₁) (step pr₂) (pop! pr₃) = cong step (⊆-assoc (pop! pr₁) pr₂ pr₃)
  ⊆-assoc (pop! pr₁) (pop! pr₂) (step pr₃) = cong step (⊆-assoc (pop! pr₁) (pop! pr₂) pr₃)
  ⊆-assoc (pop! pr₁) (pop! pr₂) (pop! pr₃) = cong pop! (⊆-assoc pr₁ pr₂ pr₃)

{- definition of membership, truncate, etc. -}

infix 10 _∈_
data _∈_ {A : Set} (σ : A) : Con A → Set where
  here! : {Γ : Con A} → σ ∈ Γ ∙ σ
  there : {Γ : Con A} {τ : A} (pr : σ ∈ Γ) → σ ∈ Γ ∙ τ

abstract

  there-inv : ∀ {A : Set} {σ τ : A} {Γ} {pr₁ pr₂ : σ ∈ Γ}
    (eq : there {τ = τ} pr₁ ≡ there pr₂) → pr₁ ≡ pr₂
  there-inv refl = refl

∈-dec : ∀ {A} {σ : A} {Γ} (pr₁ pr₂ : σ ∈ Γ) → Dec (pr₁ ≡ pr₂)
∈-dec here! here! = yes refl
∈-dec here! (there pr₂) = no (λ ())
∈-dec (there pr₁) here! = no (λ ())
∈-dec (there pr₁) (there pr₂) with ∈-dec pr₁ pr₂
... | yes p = yes (cong there p)
... | no ¬p = no (λ p → ¬p (there-inv p))

{- compatibility with inclusion -}

inc-in : ∀ {A : Set} {σ : A} {Γ Δ : Con A} → Γ ⊆ Δ → σ ∈ Γ → σ ∈ Δ
inc-in base ()
inc-in (step inc) pr = there (inc-in inc pr)
inc-in (pop! inc) here! = here!
inc-in (pop! inc) (there pr) = there (inc-in inc pr)

abstract

  inc-in-same : ∀ {A : Set} {Δ : Con A} {σ} (pr : σ ∈ Δ) → inc-in (same Δ) pr ≡ pr
  inc-in-same here! = refl
  inc-in-same (there pr) = cong there (inc-in-same pr)

  inc-in² : ∀ {A : Set} {Γ Δ Ε} {σ : A} (inc₁ : Γ ⊆ Δ) (inc₂ : Δ ⊆ Ε) (pr : σ ∈ Γ) →
            inc-in inc₂ (inc-in inc₁ pr) ≡ inc-in (⊆-trans inc₁ inc₂) pr
  inc-in² base inc₂ ()
  inc-in² (step inc₁) (step inc₂) pr = cong there (inc-in² (step inc₁) inc₂ pr)
  inc-in² (step inc₁) (pop! inc₂) pr = cong there (inc-in² inc₁ inc₂ pr)
  inc-in² (pop! inc₁) (step inc₂) pr = cong there (inc-in² (pop! inc₁) inc₂ pr)
  inc-in² (pop! inc₁) (pop! inc₂) here! = refl
  inc-in² (pop! inc₁) (pop! inc₂) (there pr) = cong there (inc-in² inc₁ inc₂ pr)

  inc-in-step : ∀ {A : Set} {Γ Δ σ} {γ : A} (inc : (Γ ∙ γ) ⊆ Δ) (pr : σ ∈ Γ) →
                inc-in (⊆-trans (step (same Γ)) inc) pr ≡ inc-in inc (there pr)
  inc-in-step {A} {ε} inc ()
  inc-in-step (step inc) pr = cong there (inc-in-step inc pr)
  inc-in-step {A} {Γ ∙ γ} (pop! inc) here! = cong there (sym (inc-in² (same (Γ ∙ γ)) inc here!))
  inc-in-step {A} {Γ ∙ γ} (pop! inc) (there pr) =
    cong there (trans (trans (sym (inc-in² (same (Γ ∙ γ)) inc (there pr)))
               (inc-in² (step (same Γ)) inc pr)) (inc-in-step inc pr))

{- properties of deletion -}

del : ∀ {A : Set} {Γ σ} (pr : σ ∈ Γ) → Con A
del {A} {ε} ()
del {A} {Γ ∙ _} here! = Γ
del {A} {Γ ∙ γ} (there pr) = (del pr) ∙ γ

pops : ∀ {A : Set} {Γ σ} (pr : σ ∈ Γ) → Con A
pops {A} {Γ ∙ _} here! = Γ
pops (there pr) = pops pr

abstract

  inc-del : ∀ {A : Set} {Γ Δ} {σ : A} (inc : Γ ⊆ Δ) (pr : σ ∈ Γ) → del pr ⊆ del (inc-in inc pr)
  inc-del base ()
  inc-del (step inc) pr = step (inc-del inc pr)
  inc-del (pop! inc) here! = inc
  inc-del (pop! inc) (there pr) = pop! (inc-del inc pr)

  inc-pops : ∀ {A : Set} {Γ Δ} {σ : A} (inc : Γ ⊆ Δ) (pr : σ ∈ Γ) → pops pr ⊆ pops (inc-in inc pr)
  inc-pops base ()
  inc-pops (step inc) pr = inc-pops inc pr
  inc-pops (pop! inc) here! = inc
  inc-pops (pop! inc) (there pr) = inc-pops inc pr
