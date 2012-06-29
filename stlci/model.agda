module stlci.model where

open import Data.Unit
open import Data.Product renaming (_×_ to _⊗_)
open import Function hiding (id)
open import Relation.Binary.PropositionalEquality renaming (subst to coerce ; subst₂ to coerce₂)

open import tools.contexts
open import tools.closures
open import stlci.definition
open import stlci.reductions

infix 10 _⊢ne_ _⊢nf_ _⊩τ_[_] _⊩ε_[_] ↑[_]_ ↓[_]_ [_]_▹⋆↑_

{- Mutual definition of neutral and normal forms.
   A neutral form is basically a stuck computation
   while a normal form is a canonical constructor for
   a type.
   These terms can obviously be translated back to usual
   terms. -}

mutual

  data _⊢nf_ (Γ : Con ty) : ty → Set where
    ⇈μ : {d : ind} (t : Γ ⊢ne μ d) → Γ ⊢nf μ d
    :λ : {σ τ : ty} (t : Γ ∙ σ ⊢nf τ) → Γ ⊢nf σ ▹ τ
    :C : {d : ind} (t : Γ ⊢nf F[ d ] (μ d)) → Γ ⊢nf μ d
-- How to deal with functors on the goal's side
    :u : {σ : ty} → Γ ⊢nf F[ ◾ ] σ
    :r : {σ : ty} (t : Γ ⊢nf σ) → Γ ⊢nf F[ [] ] σ
    :+₁ : {d₁ d₂ : ind} {σ : ty} (t : Γ ⊢nf F[ d₁ ] σ) → Γ ⊢nf F[ d₁ + d₂ ] σ
    :+₂ : {d₁ d₂ : ind} {σ : ty} (t : Γ ⊢nf F[ d₂ ] σ) → Γ ⊢nf F[ d₁ + d₂ ] σ
    :× : {d₁ d₂ : ind} {σ : ty} (t₁ : Γ ⊢nf F[ d₁ ] σ) (t₂ : Γ ⊢nf F[ d₂ ] σ) → Γ ⊢nf F[ d₁ × d₂ ] σ
-- map on functors
    mF : {d₁ d₂ : ind} {σ τ : ty} (f : Γ ⊢nf σ ▹ τ) (v : Γ ⊢ne F[ d₁ + d₂ ] σ) → Γ ⊢nf F[ d₁ + d₂ ] τ

  data _⊢ne_ (Γ : Con ty) : ty → Set where
    :v : {σ : ty} (pr : σ ∈ Γ) → Γ ⊢ne σ
    :a : {σ τ : ty} (t : Γ ⊢ne σ ▹ τ) (u : Γ ⊢nf σ) → Γ ⊢ne τ
-- pattern matching on neutral term
    p[] : {σ τ : ty} (m : Γ ⊢ne F[ [] ] σ) (f : Γ ⊢nf σ ▹ τ) → Γ ⊢ne τ
    p+ : {d₁ d₂ : ind} {σ τ : ty} (m : Γ ⊢ne F[ d₁ + d₂ ] σ)
         (f₁ : Γ ⊢nf F[ d₁ ] σ ▹ τ) (f₂ : Γ ⊢nf F[ d₂ ] σ ▹ τ) → Γ ⊢ne τ
    p× : {d₁ d₂ : ind} {σ τ : ty} (m : Γ ⊢ne F[ d₁ × d₂ ] σ)
         (f : Γ ⊢nf F[ d₁ ] σ ▹ F[ d₂ ] σ ▹ τ) → Γ ⊢ne τ
    pμ : {d : ind} {σ : ty} (m : Γ ⊢ne μ d) (f : Γ ⊢nf F[ d ] (μ d) ▹ σ) → Γ ⊢ne σ
-- induction on an inductive type
    μμ : {d : ind} {σ : ty} (m : Γ ⊢ne μ d) (t : Γ ⊢nf (F[ d ] σ) ▹ σ) → Γ ⊢ne σ

mutual

  back-nf : ∀ {Γ σ} (t : Γ ⊢nf σ) → Γ ⊢ σ
  back-nf (⇈μ t) = back-ne t
  back-nf (:λ t) = :λ (back-nf t)
  back-nf (:C t) = :C (back-nf t)
  back-nf :u = :u
  back-nf (:r t) = :r (back-nf t)
  back-nf (:+₁ t) = :+₁ (back-nf t)
  back-nf (:+₂ t) = :+₂ (back-nf t)
  back-nf (:× t u) = :× (back-nf t) (back-nf u)
  back-nf (mF f t) = mF (back-nf f) (back-ne t)

  back-ne : ∀ {Γ σ} (t : Γ ⊢ne σ) → Γ ⊢ σ
  back-ne (:v pr) = :v pr
  back-ne (:a t u) = :a (back-ne t) (back-nf u)
  back-ne (p[] m f) = p[] (back-ne m) (back-nf f)
  back-ne (p+ m f₁ f₂) = p+ (back-ne m) (back-nf f₁) (back-nf f₂)
  back-ne (p× m f) = p× (back-ne m) (back-nf f)
  back-ne (pμ m f) = pμ (back-ne m) (back-nf f)
  back-ne (μμ m t) = μμ (back-ne m) (back-nf t)

-- weakening

mutual

  weaken-nf : ∀ {Γ Δ σ} → Γ ⊆ Δ → Γ ⊢nf σ → Δ ⊢nf σ
  weaken-nf inc (⇈μ t) = ⇈μ (weaken-ne inc t)
  weaken-nf inc (:λ t) = :λ (weaken-nf (pop! inc) t)
  weaken-nf inc (:C t) = :C (weaken-nf inc t)
  weaken-nf inc :u = :u
  weaken-nf inc (:r t) = :r (weaken-nf inc t)
  weaken-nf inc (:+₁ t) = :+₁ (weaken-nf inc t)
  weaken-nf inc (:+₂ t) = :+₂ (weaken-nf inc t)
  weaken-nf inc (:× t₁ t₂) = :× (weaken-nf inc t₁) (weaken-nf inc t₂)
  weaken-nf inc (mF t m) = mF (weaken-nf inc t) (weaken-ne inc m)

  weaken-ne : ∀ {Γ Δ σ} → Γ ⊆ Δ → Γ ⊢ne σ → Δ ⊢ne σ
  weaken-ne inc (:v pr) = :v (inc-in inc pr)
  weaken-ne inc (:a t u) = :a (weaken-ne inc t) (weaken-nf inc u)
  weaken-ne inc (p[] m t) = p[] (weaken-ne inc m) (weaken-nf inc t)
  weaken-ne inc (p+ m t₁ t₂) = p+ (weaken-ne inc m) (weaken-nf inc t₁) (weaken-nf inc t₂)
  weaken-ne inc (p× m t) = p× (weaken-ne inc m) (weaken-nf inc t)
  weaken-ne inc (pμ m t) = pμ (weaken-ne inc m) (weaken-nf inc t)
  weaken-ne inc (μμ m t) = μμ (weaken-ne inc m) (weaken-nf inc t)

{- Definition of the target model for the normalization by
   evaluation. Our target model is a Kripke-style semantics
   enriched with information on the term the element of the
   model is a reduct of (which we will call "decorative term").

   There are two notions of future worlds: extensions of the
   context (as usual) and βηι-expansions of the decorative
   term. The model is closed under both of them. -}

syntax F[d]X Δ X d t = Δ ⊩F[ d ] X [ t ]

data F[d]X (Γ : Con ty) {σ} (X : ∀ Δ (s : Δ ⊢ σ) → Set) :
           (d : ind) (s : Γ ⊢ F[ d ] σ) → Set where
  :u : ∀ {t} → Γ ⊩F[ ◾ ] X [ t ]
  :r : ∀ {s t} (v : X Γ t) (r : s ▹⋆ :r t) → Γ ⊩F[ [] ] X [ s ]
  :+₁ : ∀ {d₁ d₂ s t} (v₁ : Γ ⊩F[ d₁ ] X [ t ]) (r : s ▹⋆ :+₁ t) → Γ ⊩F[ d₁ + d₂ ] X [ s ]
  :+₂ : ∀ {d₁ d₂ s t} (v₂ : Γ ⊩F[ d₂ ] X [ t ]) (r : s ▹⋆ :+₂ t) → Γ ⊩F[ d₁ + d₂ ] X [ s ]
  :× : ∀ {d₁ d₂ s t₁ t₂} (v₁ : Γ ⊩F[ d₁ ] X [ t₁ ]) (v₂ : Γ ⊩F[ d₂ ] X [ t₂ ] ) →
       (r : s ▹⋆ :× t₁ t₂) → Γ ⊩F[ d₁ × d₂ ] X [ s ]
  mF : ∀ {d₁ d₂ τ s f}
       (F : ∀ {Δ} (inc : Γ ⊆ Δ) (s : Δ ⊢ne τ) → X Δ (:a (weaken inc f) (back-ne s)))
       (t : Γ ⊢ne F[ d₁ + d₂ ] τ) (r : s ▹⋆ mF f (back-ne t)) → Γ ⊩F[ d₁ + d₂ ] X [ s ]

data _⊩μ_[_] (Δ : Con ty) (d : ind) : (t : Δ ⊢ μ d) → Set where
  :ne : ∀ {t} (v : Δ ⊢ne μ d) (r : t ▹⋆ back-ne v) → Δ ⊩μ d [ t ]
  :C : ∀ {s t} (v : Δ ⊩F[ d ] (λ Δ s → Δ ⊩μ d [ s ]) [ t ]) (r : s ▹⋆ :C t) → Δ ⊩μ d [ s ]

_⊩τ_[_] : (Γ : Con ty) (σ : ty) (t : Γ ⊢ σ) → Set
Γ ⊩τ F[ d ] σ [ t ] = Γ ⊩F[ d ] (λ Δ s → Δ ⊩τ σ [ s ]) [ t ]
Γ ⊩τ μ d [ t ] = Γ ⊩μ d [ t ]
Γ ⊩τ σ ▹ τ [ t ] = ∀ {Δ} (inc : Γ ⊆ Δ) {s : Δ ⊢ σ} (v : Δ ⊩τ σ [ s ])
                   {ts : Δ ⊢ τ} (r : Δ ⊢ τ ∋ ts ▹⋆ :a (weaken inc t) s) →
                   Δ ⊩τ τ [ ts ]

{- Environments are pointwise interpretations of context
   realizers in the model. -}

_⊩ε_[_] : (Δ Γ : Con ty) → Δ ⊩ Γ → Set
Δ ⊩ε ε [ _ ] = ⊤
Δ ⊩ε (Γ ∙ σ) [ r , ρ ] = Δ ⊩τ σ [ r ] ⊗ Δ ⊩ε Γ [ ρ ]

{- The model is closed under weakening. The termination check
   is disabled here because Agda cannot figure out that weakening
   on fixpoints is terminating.
   As usual the properties on the functors can be proved quite
   independently from the rest of the rest of the operators. -}

-- back and weaken commute

mutual

  back-weaken-nf : ∀ {Γ Δ σ} (inc : Γ ⊆ Δ) (t : Γ ⊢nf σ) →
                   back-nf (weaken-nf inc t) ≡ weaken inc (back-nf t)
  back-weaken-nf inc (⇈μ t) = back-weaken-ne inc t
  back-weaken-nf inc (:λ t) = cong :λ (back-weaken-nf (pop! inc) t)
  back-weaken-nf inc (:C t) = cong :C (back-weaken-nf inc t)
  back-weaken-nf inc :u = refl
  back-weaken-nf inc (:r t) = cong :r (back-weaken-nf inc t)
  back-weaken-nf inc (:+₁ t) = cong :+₁ (back-weaken-nf inc t)
  back-weaken-nf inc (:+₂ t) = cong :+₂ (back-weaken-nf inc t)
  back-weaken-nf inc (:× t u) = cong₂ :× (back-weaken-nf inc t) (back-weaken-nf inc u)
  back-weaken-nf inc (mF t v) = cong₂ mF (back-weaken-nf inc t) (back-weaken-ne inc v)

  back-weaken-ne : ∀ {Γ Δ σ} (inc : Γ ⊆ Δ) (t : Γ ⊢ne σ) →
                   back-ne (weaken-ne inc t) ≡ weaken inc (back-ne t)
  back-weaken-ne inc (:v pr) = refl
  back-weaken-ne inc (:a t u) = cong₂ :a (back-weaken-ne inc t) (back-weaken-nf inc u)
  back-weaken-ne inc (p[] m t) = cong₂ p[] (back-weaken-ne inc m) (back-weaken-nf inc t)
  back-weaken-ne inc (p+ m t₁ t₂) =
    cong₃ p+ (back-weaken-ne inc m) (back-weaken-nf inc t₁) (back-weaken-nf inc t₂)
  back-weaken-ne inc (p× m t) = cong₂ p× (back-weaken-ne inc m) (back-weaken-nf inc t)
  back-weaken-ne inc (pμ m t) = cong₂ pμ (back-weaken-ne inc m) (back-weaken-nf inc t)
  back-weaken-ne inc (μμ m t) = cong₂ μμ (back-weaken-ne inc m) (back-weaken-nf inc t)

⊩F-weaken : ∀ {Γ Δ d σ X} (pr : Γ ⊆ Δ) {t : Γ ⊢ F[ d ] σ}
               (wX : ∀ {s} → X Γ s → X Δ (weaken pr s))
               (v : Γ ⊩F[ d ] X [ t ]) → Δ ⊩F[ d ] X [ weaken pr t ]
⊩F-weaken pr wX :u = :u
⊩F-weaken pr wX (:r v r) = :r (wX v) (▹⋆-cong (▹-weaken pr) r)
⊩F-weaken pr wX (:+₁ v r) = :+₁ (⊩F-weaken pr wX v) (▹⋆-cong (▹-weaken pr) r)
⊩F-weaken pr wX (:+₂ v r) = :+₂ (⊩F-weaken pr wX v) (▹⋆-cong (▹-weaken pr) r)
⊩F-weaken pr wX (:× v₁ v₂ r) = :× (⊩F-weaken pr wX v₁) (⊩F-weaken pr wX v₂) (▹⋆-cong (▹-weaken pr) r)
⊩F-weaken {Γ} {Δ} {d₁ + d₂} {σ} {X} pr {s} wX (mF {._} {._} {τ} {._} {f} F v r) =
  mF (λ inc v → coerce (λ t → X _ (:a t (back-ne v))) (sym (weaken² pr inc f))
  (F (⊆-trans pr inc) v)) (weaken-ne pr v) (coerce (λ v → weaken pr s ▹⋆ mF (weaken pr f) v)
  (sym (back-weaken-ne pr v)) (▹⋆-cong (▹-weaken pr) r))

{-# NO_TERMINATION_CHECK #-}
mutual

  ⊩τ-weaken : ∀ {Γ Δ} σ (pr : Γ ⊆ Δ) {t} (v : Γ ⊩τ σ [ t ]) → Δ ⊩τ σ [ weaken pr t ]
  ⊩τ-weaken (σ ▹ τ) pr f =
    λ inc {s} v {ts} r → f (⊆-trans pr inc) v (coerce (λ t → ts ▹⋆ :a t s) (weaken² pr inc _) r)
  ⊩τ-weaken (F[ d ] σ) pr v = ⊩F-weaken pr (⊩τ-weaken σ pr) v
  ⊩τ-weaken (μ d) pr v = ⊩μ-weaken pr v

  ⊩μ-weaken : ∀ {Γ Δ d} (pr : Γ ⊆ Δ) {t} (v : Γ ⊩μ d [ t ]) → Δ ⊩μ d [ weaken pr t ]
  ⊩μ-weaken pr (:ne v r) =
    :ne (weaken-ne pr v)
    (coerce (_▹⋆_(weaken pr _)) (sym (back-weaken-ne pr v)) (▹⋆-cong (▹-weaken pr) r))
  ⊩μ-weaken pr (:C v r) = :C (⊩F-weaken pr (⊩μ-weaken pr) v) (▹⋆-cong (▹-weaken pr) r)
   -- the termination check problem is here but we don't care!

⊩ε-weaken : ∀ (Γ : Con ty) {Δ Ε} {ρ : Δ ⊩ Γ} (pr : Δ ⊆ Ε) →
             Δ ⊩ε Γ [ ρ ] → Ε ⊩ε Γ [ ⊩-weaken Γ pr ρ ]
⊩ε-weaken ε pr vs = vs
⊩ε-weaken (Γ ∙ σ) {Δ} {Ε} {r , ρ} pr (v , vs) = ⊩τ-weaken σ pr v , ⊩ε-weaken Γ pr vs

-- the model is closed under βηι-expansion

⊩F-⋆◃ : ∀ {d σ X Γ s t} (rs : Γ ⊢ F[ d ] σ ∋ s ▹⋆ t) (v : Γ ⊩F[ d ] X [ t ]) → Γ ⊩F[ d ] X [ s ]
⊩F-⋆◃ rs :u = :u
⊩F-⋆◃ rs (:r v r) = :r v (▹⋆-trans rs r)
⊩F-⋆◃ rs (:+₁ v r) = :+₁ v (▹⋆-trans rs r)
⊩F-⋆◃ rs (:+₂ v r) = :+₂ v (▹⋆-trans rs r)
⊩F-⋆◃ rs (:× v₁ v₂ r) = :× v₁ v₂ (▹⋆-trans rs r)
⊩F-⋆◃ rs (mF f v r) = mF f v (▹⋆-trans rs r)

⊩μ-⋆◃ :  ∀ {Γ d s t} (rs : Γ ⊢ μ d ∋ s ▹⋆ t) (v : Γ ⊩μ d [ t ]) → Γ ⊩μ d [ s ]
⊩μ-⋆◃ rs (:ne v r) = :ne v (▹⋆-trans rs r)
⊩μ-⋆◃ rs (:C v r) = :C v (▹⋆-trans rs r)

⊩τ-⋆◃ : ∀ τ {Γ s t} (rs : Γ ⊢ τ ∋ s ▹⋆ t) → Γ ⊩τ τ [ t ] → Γ ⊩τ τ [ s ]
⊩τ-⋆◃ (σ ▹ τ) rs f = λ inc v r → f inc v (▹⋆-trans r (▹⋆-cong (:a₁ ∘ (▹-weaken inc)) rs))
⊩τ-⋆◃ (F[ d ] τ) rs v = ⊩F-⋆◃ rs v
⊩τ-⋆◃ (μ d) rs v = ⊩μ-⋆◃ rs v

{- Once we know that the model is closed under βηι-expansion,
   we can define the pair quote / unquote that goes back and
   forth between the model and the neutral / normal forms.
   This is where the η-expansion happens. -}

↑F[_,_]_[_] : ∀ {Γ} d σ {X} {t : Γ ⊢ F[ d ] σ}
              (↑X : ∀ {Δ} {s} (pr : Γ ⊆ Δ) → X Δ s → Δ ⊢nf σ) →
              Γ ⊩F[ d ] X [ t ] → Γ ⊢nf F[ d ] σ
↑F[ ◾ , σ ] ↑X [ :u ] = :u
↑F[ [] , σ ] ↑X [ :r v r ] = :r (↑X (same _) v)
↑F[ d₁ + d₂ , σ ] ↑X [ :+₁ v r ] = :+₁ (↑F[ d₁ , σ ] ↑X [ v ])
↑F[ d₁ + d₂ , σ ] ↑X [ :+₂ v r ] = :+₂ (↑F[ d₂ , σ ] ↑X [ v ])
↑F[ d₁ × d₂ , σ ] ↑X [ :× v₁ v₂ r ] = :× (↑F[ d₁ , σ ] ↑X [ v₁ ]) (↑F[ d₂ , σ ] ↑X [ v₂ ])
↑F[ d₁ + d₂ , σ ] ↑X [ mF f v r ] = mF (:λ (↑X (step (same _)) (f (step (same _)) (:v here!)))) v

F[_,_]_▹⋆↑[_]_ : ∀ d σ {Γ X} {↑X : ∀ {Δ} {s} (pr : Γ ⊆ Δ) → X Δ s → Δ ⊢nf σ} (t : Γ ⊢ F[ d ] σ)
                 (⇈X : ∀ {Δ s pr} (v : X Δ s) → s ▹⋆ back-nf (↑X pr v)) (v : Γ ⊩F[ d ] X [ t ]) →
                 t ▹⋆ back-nf (↑F[ d , σ ] ↑X [ v ])
F[ ◾ , σ ] t ▹⋆↑[ ⇈X ] :u = step :u refl
F[ [] , σ ] t ▹⋆↑[ ⇈X ] :r v r = ▹⋆-trans r (▹⋆-cong :r (⇈X v))
F[ d₁ + d₂ , σ ] t ▹⋆↑[ ⇈X ] :+₁ v r = ▹⋆-trans r (▹⋆-cong :+₁ (F[ d₁ , σ ] _ ▹⋆↑[ ⇈X ] v))
F[ d₁ + d₂ , σ ] t ▹⋆↑[ ⇈X ] :+₂ v r = ▹⋆-trans r (▹⋆-cong :+₂ (F[ d₂ , σ ] _ ▹⋆↑[ ⇈X ] v))
F[ d₁ × d₂ , σ ] t ▹⋆↑[ ⇈X ] :× v₁ v₂ r =
  ▹⋆-trans r (▹⋆-trans (▹⋆-cong :×₁ (F[ d₁ , σ ] _ ▹⋆↑[ ⇈X ] v₁))
  (▹⋆-cong :×₂ (F[ d₂ , σ ] _ ▹⋆↑[ ⇈X ] v₂)))
F[ d₁ + d₂ , σ ] t ▹⋆↑[ ⇈X ] mF f v r =
  ▹⋆-trans r (▹⋆-cong {f = λ t → mF t (back-ne v)} mF₂ (step (:ηλ _)
  (▹⋆-cong :λ (⇈X (f (step (⊆-refl _)) (:v here!))))))

{-# NO_TERMINATION_CHECK #-}
↑μ[_]_ : ∀ {Γ} d {t} (v : Γ ⊩μ d [ t ]) → Γ ⊢nf μ d
↑μ[ d ] :ne v r = ⇈μ v
↑μ[ d ] :C v r = :C ↑F[ d , μ d ] (λ _ → ↑μ[_]_ d) [ v ]

{-# NO_TERMINATION_CHECK #-}
μ[_]_▹⋆↑_ : ∀ {Γ} d t (v : Γ ⊩μ d [ t ]) → t ▹⋆ back-nf (↑μ[ d ] v)
μ[ d ] t ▹⋆↑ :ne v r = r
μ[ d ] t ▹⋆↑ :C v r =
  ▹⋆-trans r (▹⋆-cong :C (F[ d , μ d ] _ ▹⋆↑[ (λ {Δ} {s} v → μ[ d ] s ▹⋆↑ v) ] v))

mutual

  ↑[_]_ : ∀ {Γ} σ {t : Γ ⊢ σ} → Γ ⊩τ σ [ t ] → Γ ⊢nf σ
  ↑[ F[ d ] σ ] v = ↑F[ d , σ ] (λ _ → ↑[_]_ σ) [ v ]
  ↑[ μ d ] v = ↑μ[ d ] v
  ↑[ σ ▹ τ ] v = :λ (↑[ τ ] v (step (same _)) (↓[ σ ] :v here!) refl)

  ↓[_]_ : ∀ {Γ} σ (t : Γ ⊢ne σ) → Γ ⊩τ σ [ back-ne t ]
  ↓[ F[ ◾ ] σ ] t = :u
  ↓[ F[ [] ] σ ] t = 
    :r (⊩τ-⋆◃ σ (▹⋆-cong {f = λ f → p[] (back-ne t) (:λ f)} (λ p → :p[]₂ (:λ p))
       ([ σ ] :v here! ▹⋆↑ (↓[ σ ] :v here!)))
       -- value of the hole: p[] t id
       (↓[ σ ] p[] t (:λ (↑[ σ ] (↓[ σ ] (:v here!))))))
    (step (:ηr (back-ne t)) refl)
  ↓[ F[ d₁ × d₂ ] σ ] t = 
    :× (⊩τ-⋆◃ (F[ d₁ ] σ) (▹⋆-cong {f = λ f → p× (back-ne t) (:λ (:λ f))} (λ p → :p×₂ (:λ (:λ p)))
       ([ _ ] :v (there here!) ▹⋆↑ ↓[ _ ] :v (there here!)))
       -- value of the first component: p× t fst
       (↓[ F[ d₁ ] σ ] p× t (:λ (:λ (↑[ _ ] (↓[ _ ] :v (there here!)))))))
      
       (⊩τ-⋆◃ (F[ d₂ ] σ) (▹⋆-cong {f = λ f → p× (back-ne t) (:λ (:λ f))} (λ p → :p×₂ (:λ (:λ p)))
       ([ _ ] :v here! ▹⋆↑ ↓[ _ ] :v here!))
       -- value of the second component: p× t snd
       (↓[ F[ d₂ ] σ ] p× t (:λ (:λ (↑[ _ ] (↓[ _ ] :v here!))))))
    (step (:η× (back-ne t)) refl)
  ↓[ F[ d₁ + d₂ ] σ ] t = mF (λ inc s → ⊩τ-⋆◃ σ (step (:β _ _) refl) (↓[ σ ] s)) t (step mFid refl)
  ↓[ μ d ] t = :ne t refl
  ↓[ σ ▹ τ ] t =
    λ {Δ} inc {s} v {ts} r →
  -- administrative bullshit
    ⊩τ-⋆◃ τ (▹⋆-trans r (▹⋆-cong {f = λ s → :a (weaken inc (back-ne t)) s} :a₂ ([ σ ] s ▹⋆↑ v)))
    (coerce (λ t → Δ ⊩τ τ [ :a t (back-nf (↑[ σ ] v)) ]) (back-weaken-ne inc t)
  -- actual computation
    (↓[ τ ] :a (weaken-ne inc t) (↑[ σ ] v)))

  [_]_▹⋆↑_ : ∀ σ {Γ} (t : Γ ⊢ σ) (v : Γ ⊩τ σ [ t ]) → t ▹⋆ back-nf (↑[ σ ] v)
  [ F[ d ] σ ] t ▹⋆↑ v = F[ d , σ ] t ▹⋆↑[ [_]_▹⋆↑_ σ _ ] v
  [ μ d ] t ▹⋆↑ v = μ[ d ] t ▹⋆↑ v
  [ σ ▹ τ ] t ▹⋆↑ v = step (:ηλ t) (▹⋆-cong :λ ([ τ ] :a (weaken _ t) (:v here!) ▹⋆↑ v _ _ refl))

-- definition of the trivial environment

⊩τvar : {Γ : Con ty} (σ : ty) → (Γ ∙ σ) ⊩τ σ [ :v here! ]
⊩τvar σ = ↓[ σ ] (:v here!)

Γ⊩ε_ : (Γ : Con ty) → Γ ⊩ε Γ [ Γ⊩ Γ ]
Γ⊩ε ε = tt
Γ⊩ε (Γ ∙ γ) = ⊩τvar γ , ⊩ε-weaken Γ (step (same Γ)) (Γ⊩ε Γ)

-- neutral map

⊩τ-mF : ∀ {d Γ σ τ f}
  (F : ∀ {Δ} (inc : Γ ⊆ Δ) (s : Δ ⊢ne τ) → Δ ⊩τ σ [ :a (weaken inc f) (back-ne s) ])
  (t : Γ ⊢ne F[ d ] τ) → Γ ⊩τ F[ d ] σ [ mF f (back-ne t) ]
⊩τ-mF {◾} F t = :u
⊩τ-mF {[]} F t =
  :r (F (same _) (p[] t (:λ (↑[ _ ] (↓[ _ ] :v here!)))))
     (step (mF₁ (:ηr (back-ne t))) (step mF[]
     (≡-step (cong (λ t → :r (:a t _)) (sym (weaken-same _)))
     (▹⋆-cong {f = λ f → :r (:a _ (p[] _ (:λ f)))} (λ p → :r (:a₂ (:p[]₂ (:λ p))))
              ([ _ ] :v here! ▹⋆↑ ↓[ _ ] :v here!)))))
⊩τ-mF {d₁ × d₂} F t =
  :× (⊩τ-mF {d₁} F (p× t (:λ (:λ (↑[ _ ] (↓[ _ ] :v (there here!)))))))
     (⊩τ-mF {d₂} F (p× t (:λ (:λ (↑[ _ ] (↓[ _ ] :v here!))))))
     (step (mF₁ (:η× (back-ne t))) (step mF× (▹⋆-trans
     (▹⋆-cong {f = λ f → :× (mF _ (p× _ (:λ (:λ f)))) _} (λ p → :×₁ (mF₁ (:p×₂ (:λ (:λ p)))))
              ([ _ ] :v (there here!) ▹⋆↑ ↓[ _ ] :v (there here!)))
     (▹⋆-cong {f = λ f → :× _ (mF _ (p× _ (:λ (:λ f))))} (λ p → :×₂ (mF₁ (:p×₂ (:λ (:λ p)))))
              ([ _ ] :v here! ▹⋆↑ ↓[ _ ] :v here!)))))
⊩τ-mF {d₁ + d₂} F t = mF F t refl