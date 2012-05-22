module tools.closures where

data reftranclos {A : Set} (P : A → A → Set) : A → A → Set where
  refl : {t : A} → reftranclos P t t
  step : {s t u : A} (p : P s t) (p₁ : reftranclos P t u) → reftranclos P s u

_▹[_]⋆_ : {A : Set} (s : A) (P : A → A → Set) (t : A) → Set
s ▹[ P ]⋆ t = reftranclos P s t

▹⋆-cong : ∀ {A B : Set} {P Q} {f : A → B} (cg : {a a' : A} (p : P a a') → Q (f a) (f a')) →
          {s t : A} (p : s ▹[ P ]⋆ t) → f s ▹[ Q ]⋆ f t
▹⋆-cong cg refl = refl
▹⋆-cong cg (step p p₁) = step (cg p) (▹⋆-cong cg p₁)

▹⋆-trans : ∀ {A : Set} {P} {s t u : A} (p₁ : s ▹[ P ]⋆ t) (p₂ : t ▹[ P ]⋆ u) → s ▹[ P ]⋆ u
▹⋆-trans refl p₂ = p₂
▹⋆-trans (step p p₁) p₂ = step p (▹⋆-trans p₁ p₂)

▹⋆-idempotent : ∀ {A : Set} {P} {s t : A} (p : s ▹[ reftranclos P ]⋆ t) → s ▹[ P ]⋆ t
▹⋆-idempotent refl = refl
▹⋆-idempotent (step p p₁) = ▹⋆-trans p (▹⋆-idempotent p₁)

data refsymtranclos {A : Set} (P : A → A → Set) : A → A → Set where
  refl : {t : A} → refsymtranclos P t t
  lstep : {s t u : A} (p : P s t) (p₁ : refsymtranclos P t u) → refsymtranclos P s u
  rstep : {s t u : A} (p : P t s) (p₁ : refsymtranclos P t u) → refsymtranclos P s u

_≡[_]⋆_ : {A : Set} (s : A) (P : A → A → Set) (t : A) → Set
s ≡[ P ]⋆ t = refsymtranclos P s t

▹≡⋆ : ∀ {A : Set} {P} {s t : A} (ps : s ▹[ P ]⋆ t) → s ≡[ P ]⋆ t
▹≡⋆ refl = refl
▹≡⋆ (step p ps) = lstep p (▹≡⋆ ps)

≡⋆-cong : ∀ {A B : Set} {P Q} {f : A → B} (cg : {a a' : A} (p : P a a') → Q (f a) (f a')) →
          {s t : A} (p : s ≡[ P ]⋆ t) → f s ≡[ Q ]⋆ f t
≡⋆-cong cg refl = refl
≡⋆-cong cg (lstep p p₁) = lstep (cg p) (≡⋆-cong cg p₁)
≡⋆-cong cg (rstep p p₁) = rstep (cg p) (≡⋆-cong cg p₁)

≡⋆-trans : ∀ {A : Set} {P} {s t u : A} (p₁ : s ≡[ P ]⋆ t) (p₂ : t ≡[ P ]⋆ u) → s ≡[ P ]⋆ u
≡⋆-trans refl p₂ = p₂
≡⋆-trans (lstep p p₁) p₂ = lstep p (≡⋆-trans p₁ p₂)
≡⋆-trans (rstep p p₁) p₂ = rstep p (≡⋆-trans p₁ p₂)

≡⋆-sym : ∀ {A : Set} {P} {s t : A} (ps : s ≡[ P ]⋆ t) → t ≡[ P ]⋆ s
≡⋆-sym refl = refl
≡⋆-sym (lstep p ps) = ≡⋆-trans (≡⋆-sym ps) (rstep p refl)
≡⋆-sym (rstep p ps) = ≡⋆-trans (≡⋆-sym ps) (lstep p refl)

≡⋆-idempotent : ∀ {A : Set} {P} {s t : A} (ps : s ≡[ refsymtranclos P ]⋆ t) → s ≡[ P ]⋆ t
≡⋆-idempotent refl = refl
≡⋆-idempotent (lstep p ps) = ≡⋆-trans p (≡⋆-idempotent ps)
≡⋆-idempotent (rstep p ps) = ≡⋆-trans (≡⋆-sym p) (≡⋆-idempotent ps)
