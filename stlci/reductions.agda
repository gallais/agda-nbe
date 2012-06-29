module stlci.reductions where

open import Data.Product renaming (_×_ to _⊗_)
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

open import tools.contexts
open import tools.closures
open import stlci.definition

{- Definition of the (quite massive) reduction relation.
   ∙ ι rules deal with the reduction of pattern matchings.
   ∙ map-fusion rules deal with the combination of maps and
     pattern-matchings
   ∙ all the elements of the unit type are identified
   ∙ the rest is quite common (congruence, βη). -}

data _⊢_∋_▹_ (Γ : Con ty) : (τ : ty) (s t : Γ ⊢ τ) → Set where
-- congruence rules
  :λ : ∀ {σ τ s t} (r : Γ ∙ σ ⊢ τ ∋ s ▹ t) → Γ ⊢ σ ▹ τ ∋ :λ s ▹ :λ t
  :a₁ : ∀ {σ τ f g s} (r : Γ ⊢ σ ▹ τ ∋ f ▹ g) →  Γ ⊢ τ ∋ :a f s ▹ :a g s
  :a₂ : ∀ {σ τ f s t} (r : Γ ⊢ σ ∋ s ▹ t) →  Γ ⊢ τ ∋ :a f s ▹ :a f t
  :C : ∀ {d s t} (r : Γ ⊢ F[ d ] (μ d) ∋ s ▹ t) → Γ ⊢ μ d ∋ :C s ▹ :C t
  :r : ∀ {σ s t} (r : Γ ⊢ σ ∋ s ▹ t) → Γ ⊢ F[ [] ] σ ∋ :r s ▹ :r t
  :+₁ : ∀ {d₁ d₂ σ s t} (r : Γ ⊢ F[ d₁ ] σ ∋ s ▹ t) → Γ ⊢ F[ d₁ + d₂ ] σ ∋ :+₁ s ▹ :+₁ t
  :+₂ : ∀ {d₁ d₂ σ s t} (r : Γ ⊢ F[ d₂ ] σ ∋ s ▹ t) → Γ ⊢ F[ d₁ + d₂ ] σ ∋ :+₂ s ▹ :+₂ t
  :×₁ : ∀ {d₁ d₂ σ b s t} (r : Γ ⊢ F[ d₁ ] σ ∋ s ▹ t) → Γ ⊢ F[ d₁ × d₂ ] σ ∋ :× s b ▹ :× t b
  :×₂ : ∀ {d₁ d₂ σ a s t} (r : Γ ⊢ F[ d₂ ] σ ∋ s ▹ t) → Γ ⊢ F[ d₁ × d₂ ] σ ∋ :× a s ▹ :× a t
  mF₁ : ∀ {d σ τ m n t} (r : Γ ⊢ F[ d ] σ ∋ m ▹ n) → Γ ⊢ F[ d ] τ ∋ mF t m ▹ mF t n
  mF₂ : ∀ {d σ τ m t₁ t₂} (r : Γ ⊢ σ ▹ τ ∋ t₁ ▹ t₂) → Γ ⊢ F[ d ] τ ∋ mF t₁ m ▹ mF t₂ m
  :p[]₁ : ∀ {σ τ m n t} (r : Γ ⊢ F[ [] ] σ ∋ m ▹ n) → Γ ⊢ τ ∋ p[] m t ▹ p[] n t
  :p[]₂ : ∀ {σ τ m t₁ t₂} (r : Γ ⊢ σ ▹ τ ∋ t₁ ▹ t₂) → Γ ⊢ τ ∋ p[] m t₁ ▹ p[] m t₂
  :p+₁ : ∀ {d₁ d₂ σ τ m n t₁ t₂} (r : Γ ⊢ F[ d₁ + d₂ ] σ ∋ m ▹ n) → Γ ⊢ τ ∋ p+ m t₁ t₂ ▹ p+ n t₁ t₂
  :p+₂ : ∀ {d₁ d₂ σ τ} {m : Γ ⊢ F[ d₁ + d₂ ] σ} {t₁ t₂ u} (r : Γ ⊢ F[ d₁ ] σ ▹ τ ∋ t₁ ▹ t₂) →
         Γ ⊢ τ ∋ p+ m t₁ u ▹ p+ m t₂ u
  :p+₃ : ∀ {d₁ d₂ σ τ} {m : Γ ⊢ F[ d₁ + d₂ ] σ} {t u₁ u₂} (r : Γ ⊢ F[ d₂ ] σ ▹ τ ∋ u₁ ▹ u₂) →
         Γ ⊢ τ ∋ p+ m t u₁ ▹ p+ m t u₂
  :p×₁ : ∀ {d₁ d₂ σ τ m n t} (r : Γ ⊢ F[ d₁ × d₂ ] σ ∋ m ▹ n) → Γ ⊢ τ ∋ p× m t ▹ p× n t
  :p×₂ : ∀ {d₁ d₂ σ τ m t₁ t₂} (r : Γ ⊢ F[ d₁ ] σ ▹ F[ d₂ ] σ ▹ τ ∋ t₁ ▹ t₂) →
         Γ ⊢ τ ∋ p× m t₁ ▹ p× m t₂
  :pμ₁ : ∀ {d τ m n t} (r : Γ ⊢ μ d ∋ m ▹ n) → Γ ⊢ τ ∋ pμ m t ▹ pμ n t
  :pμ₂ : ∀ {d τ m t₁ t₂} (r : Γ ⊢ F[ d ] (μ d) ▹ τ ∋ t₁ ▹ t₂) → Γ ⊢ τ ∋ pμ m t₁ ▹ pμ m t₂
  :μμ₁ : ∀ {d σ m n t} (r : Γ ⊢ μ d ∋ m ▹ n) → Γ ⊢ σ ∋ μμ m t ▹ μμ n t
  :μμ₂ : ∀ {d σ m t₁ t₂} (r : Γ ⊢ F[ d ] σ ▹ σ ∋ t₁ ▹ t₂) → Γ ⊢ σ ∋ μμ m t₁ ▹ μμ m t₂
-- βι rules
  :β : ∀ {σ τ} t (s : Γ ⊢ σ) → Γ ⊢ τ ∋ :a (:λ t) s ▹ β-reduce t s
  mF[] : ∀ {σ τ m} {t : Γ ⊢ σ ▹ τ} → Γ ⊢ F[ [] ] τ ∋ mF t (:r m) ▹ :r (:a t m)
  mF+₁ : ∀ {d₁ d₂ σ τ m} {t : Γ ⊢ σ ▹ τ} → Γ ⊢ F[ d₁ + d₂ ] τ ∋ mF t (:+₁ m) ▹ :+₁ (mF t m)
  mF+₂ : ∀ {d₁ d₂ σ τ m} {t : Γ ⊢ σ ▹ τ} → Γ ⊢ F[ d₁ + d₂ ] τ ∋ mF t (:+₂ m) ▹ :+₂ (mF t m)
  mF× : ∀ {d₁ d₂ σ τ m n} {t : Γ ⊢ σ ▹ τ} → Γ ⊢ F[ d₁ × d₂ ] τ ∋ mF t (:× m n) ▹ :× (mF t m) (mF t n)
  :p[] : ∀ {σ τ s t} → Γ ⊢ τ ∋ p[] {Γ} {σ} (:r s) t ▹ :a t s
  :p+l : ∀ {d₁ d₂ σ τ m t₁ t₂} → Γ ⊢ τ ∋ p+ {Γ} {d₁} {d₂} {σ} (:+₁ m) t₁ t₂ ▹ :a t₁ m
  :p+r : ∀ {d₁ d₂ σ τ m t₁ t₂} → Γ ⊢ τ ∋ p+ {Γ} {d₁} {d₂} {σ} (:+₂ m) t₁ t₂ ▹ :a t₂ m
  :p×  : ∀ {d₁ d₂ σ τ m n t} → Γ ⊢ τ ∋ p× {Γ} {d₁} {d₂} {σ} (:× m n) t ▹ :a (:a t m) n
  :pμ  : ∀ {d τ m t} → Γ ⊢ τ ∋ pμ {Γ} {d} (:C m) t ▹ :a t m
  :μμ  : ∀ {d σ m t} → Γ ⊢ σ ∋ μμ {Γ} {d} {σ} (:C m) t ▹
         :a t (mF (:λ (μμ (:v here!) (weaken (step (same Γ)) t))) m)
-- map fusion rules
  mFid : ∀ {d σ x} → Γ ⊢ F[ d ] σ ∋ x ▹ mF id x
  mF² : ∀ {d σ τ υ} (g : Γ ⊢ τ ▹ υ) (f : Γ ⊢ σ ▹ τ) x →
        Γ ⊢ F[ d ] υ ∋ mF g (mF f x) ▹ mF (g :∘ f) x
  mFp[] : ∀ {σ τ υ d m} f (t : Γ ⊢ σ ▹ F[ d ] τ) →
          Γ ⊢ F[ d ] υ ∋ mF f (p[] m t) ▹ p[] m mF[ f :∘ t ]
  mFp+ : ∀ {σ τ υ d d₁ d₂ m} f (t₁ : Γ ⊢ F[ d₁ ] σ ▹ F[ d ] τ) (t₂ : Γ ⊢ F[ d₂ ] σ ▹ F[ d ] τ) →
         Γ ⊢ F[ d ] υ ∋ mF f (p+ m t₁ t₂) ▹ p+ m mF[ f :∘ t₁ ] mF[ f :∘ t₂ ]
  mFp× : ∀ {σ τ υ d d₁ d₂ m} f (t : Γ ⊢ F[ d₁ ] σ ▹ F[ d₂ ] σ ▹ F[ d ] τ) →
         Γ ⊢ F[ d ] υ ∋ mF f (p× m t) ▹ p× m mF₂[ f :∘ t ]
  mFpμ : ∀ {σ τ d d' m} f (t : Γ ⊢ F[ d' ] (μ d') ▹ F[ d ] σ) →
         Γ ⊢ F[ d ] τ ∋ mF f (pμ m t) ▹ pμ m mF[ f :∘ t ]
  p[]mF : ∀ {σ τ υ m} (f : Γ ⊢ σ ▹ τ) t → Γ ⊢ υ ∋ p[] (mF f m) t ▹ p[] m (t :∘ f)
  p+mF : ∀ {σ τ υ d₁ d₂} {m : Γ ⊢ F[ d₁ + d₂ ] σ} (f : Γ ⊢ σ ▹ τ) t₁ t₂ →
         Γ ⊢ υ ∋ p+ (mF f m) t₁ t₂ ▹ p+ m (t₁ :∘mF[ f ]) (t₂ :∘mF[ f ])
  p×mF : ∀ {σ τ υ d₁ d₂} {m : Γ ⊢ F[ d₁ × d₂ ] σ} (f : Γ ⊢ σ ▹ τ) t →
         Γ ⊢ υ ∋ p× (mF f m) t ▹ p× m (t :∘mF₂[ f ])
-- η rules
  :u : ∀ {σ s} → Γ ⊢ F[ ◾ ] σ ∋ s ▹ :u
  :ηλ : ∀ {σ τ} t → Γ ⊢ σ ▹ τ ∋ t ▹ η-expand t
  :η× : ∀ {d₁ d₂ σ} t → Γ ⊢ F[ d₁ × d₂ ] σ ∋ t ▹ :× (fst t) (snd t)
  :ηr : ∀ {σ} t → Γ ⊢ F[ [] ] σ ∋ t ▹ :r (p[] t id)

{- A bunch of notation for the reflexive, (symmetric,)
   transitive closures of _⊢_∋_▹_. -}

_⊢_∋_▹⋆_ : ∀ Γ τ (s t : Γ ⊢ τ) → Set
Γ ⊢ τ ∋ s ▹⋆ t = s ▹[ _⊢_∋_▹_ Γ τ ]⋆ t

infix 11 _▹⋆_

_▹⋆_ : ∀ {Γ τ} (s t : Γ ⊢ τ) → Set
_▹⋆_ {Γ} {τ} s t = Γ ⊢ τ ∋ s ▹⋆ t

_≡βη_ : ∀ {Γ τ} (s t : Γ ⊢ τ) → Set
_≡βη_ {Γ} {τ} s t = s ≡[ _⊢_∋_▹_ Γ τ ]⋆ t

-- compatibility of the reduction relation with weakening

▹-weaken : ∀ {Γ Δ τ s t} (pr : Γ ⊆ Δ) (r : Γ ⊢ τ ∋ s ▹ t) →
           Δ ⊢ τ ∋ weaken pr s ▹ weaken pr t
▹-weaken pr (:λ r) = :λ (▹-weaken (pop! pr) r)
▹-weaken pr (:a₁ r) = :a₁ (▹-weaken pr r)
▹-weaken pr (:a₂ r) = :a₂ (▹-weaken pr r)
▹-weaken pr (:C r) = :C (▹-weaken pr r)
▹-weaken pr (:r r) = :r (▹-weaken pr r)
▹-weaken pr (:+₁ r) = :+₁ (▹-weaken pr r)
▹-weaken pr (:+₂ r) = :+₂ (▹-weaken pr r)
▹-weaken pr (:×₁ r) = :×₁ (▹-weaken pr r)
▹-weaken pr (:×₂ r) = :×₂ (▹-weaken pr r)
▹-weaken pr (mF₁ r) = mF₁ (▹-weaken pr r)
▹-weaken pr (mF₂ r) = mF₂ (▹-weaken pr r)
▹-weaken pr (:p[]₁ r) = :p[]₁ (▹-weaken pr r)
▹-weaken pr (:p[]₂ r) = :p[]₂ (▹-weaken pr r)
▹-weaken pr (:p+₁ r) = :p+₁ (▹-weaken pr r)
▹-weaken pr (:p+₂ r) = :p+₂ (▹-weaken pr r)
▹-weaken pr (:p+₃ r) = :p+₃ (▹-weaken pr r)
▹-weaken pr (:p×₁ r) = :p×₁ (▹-weaken pr r)
▹-weaken pr (:p×₂ r) = :p×₂ (▹-weaken pr r)
▹-weaken pr (:pμ₁ r) = :pμ₁ (▹-weaken pr r)
▹-weaken pr (:pμ₂ r) = :pμ₂ (▹-weaken pr r)
▹-weaken pr (:μμ₁ r) = :μμ₁ (▹-weaken pr r)
▹-weaken pr (:μμ₂ r) = :μμ₂ (▹-weaken pr r)
▹-weaken pr mF[] = mF[]
▹-weaken pr mF+₁ = mF+₁
▹-weaken pr mF+₂ = mF+₂
▹-weaken pr mF× = mF×
▹-weaken pr :p[] = :p[]
▹-weaken pr :p+l = :p+l
▹-weaken pr :p+r = :p+r
▹-weaken pr :p× = :p×
▹-weaken pr :pμ = :pμ
▹-weaken {Γ} {Δ} {τ} {μμ (:C m) t₁} pr :μμ =
  coerce (λ t → Δ ⊢ τ ∋ μμ (:C (weaken pr m)) (weaken pr t₁) ▹ :a (weaken pr t₁)
  (mF (:λ (μμ (:v here!) t)) (weaken pr m))) (trans (weaken² pr _ t₁) (trans
  (cong (λ pr → weaken pr t₁) (sym (⊆-step-same _))) (sym (weaken² _ (pop! pr) t₁)))) :μμ
▹-weaken pr :u = :u
▹-weaken pr mFid = mFid
▹-weaken pr (mF² g f x) rewrite :∘-weaken pr g f = mF² (weaken pr g) (weaken pr f) (weaken pr x)
▹-weaken pr (mFp[] f t) rewrite mFc-weaken pr f t = mFp[] (weaken pr f) (weaken pr t)
▹-weaken pr (mFp+ f t₁ t₂) rewrite mFc-weaken pr f t₁ | mFc-weaken pr f t₂ =
  mFp+ (weaken pr f) (weaken pr t₁) (weaken pr t₂)
▹-weaken pr (mFp× f t) rewrite mF₂c-weaken pr f t = mFp× (weaken pr f) (weaken pr t)
▹-weaken pr (mFpμ f t) rewrite mFc-weaken pr f t = mFpμ (weaken pr f) (weaken pr t)
▹-weaken pr (p[]mF f t) rewrite :∘-weaken pr t f = p[]mF (weaken pr f) (weaken pr t)
▹-weaken pr (p+mF f t₁ t₂) rewrite cmF-weaken pr t₁ f | cmF-weaken pr t₂ f =
  p+mF (weaken pr f) (weaken pr t₁) (weaken pr t₂)
▹-weaken pr (p×mF f t) rewrite cmF₂-weaken pr t f = p×mF (weaken pr f) (weaken pr t)
▹-weaken pr (:ηλ t) rewrite η-weaken pr t = :ηλ (weaken pr t)
▹-weaken pr (:η× t) = :η× (weaken pr t)
▹-weaken pr (:ηr t) = :ηr (weaken pr t)
▹-weaken pr (:β t s) rewrite β-weaken pr t s = :β (weaken (pop! pr) t) (weaken pr s)
