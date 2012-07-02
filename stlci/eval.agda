module stlci.eval where

open import Data.Empty
open import Data.Unit
open import Data.Product renaming (_×_ to _⊗_)
open import Function
open import Relation.Binary.PropositionalEquality renaming (subst to coerce ; subst₂ to coerce₂)

open import tools.contexts
open import tools.closures
open import stlci.definition
open import stlci.reductions
open import stlci.model

{- Definition of the evaluation function. We go through
   various helper functions in order to explain what the
   behaviour of the common constructors is.
   This is were βι-reductions and the map-fusion laws are
   applied. -}

lookup : ∀ Γ {Δ σ ρ} (pr : σ ∈ Γ) → Δ ⊩ε Γ [ ρ ] → Δ ⊩τ σ [ get pr ρ ]
lookup ε () ρ
lookup (_ ∙ σ) here! (v , _) = v
lookup (Γ ∙ _) (there pr) (_ , ρ) = lookup Γ pr ρ

-- map

vmap : ∀ {τ σ Γ d} f (t : Γ ⊢ F[ d ] σ ) (F : Γ ⊩τ σ ▹ τ [ f ]) (T : Γ ⊩τ F[ d ] σ [ t ]) →
       Γ ⊩τ F[ d ] τ [ mF f t ]
vmap f t F :u = :u
vmap f t F (:r {._} {s} T r) =
   :r (F (same _) T refl) (▹⋆-trans (▹⋆-cong mF₁ r)
   (step mF[] (coerce (λ t → :r (:a f s) ▹⋆ :r (:a t _)) (sym (weaken-same _)) refl)))
vmap f t F (:+₁ T₁ r) = :+₁ (vmap f _ F T₁) (▹⋆-trans (▹⋆-cong mF₁ r) (step mF+₁ refl))
vmap f t F (:+₂ T₂ r) = :+₂ (vmap f _ F T₂) (▹⋆-trans (▹⋆-cong mF₁ r) (step mF+₂ refl))
vmap f t F (:× T₁ T₂ r) = :× (vmap f _ F T₁) (vmap f _ F T₂) (▹⋆-trans (▹⋆-cong mF₁ r) (step mF× refl))
vmap {τ} f t F (mF {_} {_} {_} {._} {t'} g T r) =
  mF (λ {Δ} inc s → F inc (g inc s)
  -- coercions
  (step (:β _ (back-ne s)) (coerce₂
  (λ t u → :a t (:a u (back-ne s)) ▹⋆ :a (weaken inc f) (:a (weaken inc t') (back-ne s)))
  (subst-pop f (back-ne s) inc) (subst-pop t' (back-ne s) inc) refl)))
 -- rest of the computation
   T (▹⋆-trans (▹⋆-cong mF₁ r) (step (mF² f _ (back-ne T)) refl))

-- fold

{-# NO_TERMINATION_CHECK #-}
vrec : ∀ {Γ} d {m} σ {f} (M : Γ ⊩τ μ d [ m ]) (F : Γ ⊩τ F[ d ] σ ▹ σ [ f ]) → Γ ⊩τ σ [ μμ m f ]
vrec d σ {f} (:ne v r) F =
  ⊩τ-⋆◃ σ (▹⋆-trans (▹⋆-cong :μμ₁ r)
  (▹⋆-cong {f = μμ (back-ne v)} :μμ₂ (step (:ηλ f) (▹⋆-cong {f = :λ} :λ ([ σ ] _ ▹⋆↑ _)))))
  (↓[ σ ] μμ v (:λ (↑[ σ ] F (step (same _)) (↓[ F[ d ] σ ] :v here!) refl)))
vrec {Γ} d σ {f} (:C {._} {t} v r) F =
  F (same _) (vmap (:λ (μμ (:v here!) (weaken (step (same _)) f))) _
  (λ {Δ} inc {s} v {ts} r → ⊩τ-⋆◃ σ (▹⋆-trans r (step (:β _ _)
  (coerce (λ t → μμ s t ▹⋆ μμ s (weaken inc f)) (subst-pop f s inc) refl)))
  (vrec d σ v (λ {Δ'} inc' {s'} v' {ts'} r' →
  F (⊆-trans inc inc') v' (coerce (λ f → ts' ▹⋆ :a f s') (weaken² inc inc' f) r')))) v)
  (▹⋆-trans (▹⋆-cong :μμ₁ r) (step :μμ (coerce (λ f' →
  :a f' (mF (:λ (μμ (:v here!) (weaken (step (same Γ)) f))) t) ▹⋆
  :a (weaken (same Γ) f) (mF (:λ (μμ (:v here!) (weaken (step (same Γ)) f))) t)) (weaken-same f) refl)))

-- app

vapp : ∀ {Γ τ σ} f x (vf : Γ ⊩τ σ ▹ τ [ f ]) (vx : Γ ⊩τ σ [ x ]) → Γ ⊩τ τ [ :a f x ]
vapp {Γ} {τ} f x vf vx = coerce (λ f → Γ ⊩τ τ [ :a f x ]) (weaken-same f) (vf (same Γ) vx refl)

vmu : ∀ {Γ d m} τ {f} (M : Γ ⊩τ μ d [ m ]) (F : Γ ⊩τ F[ d ] (μ d) ▹ τ [ f ]) → Γ ⊩τ τ [ pμ m f ]
vmu {Γ} {d} τ {f} (:ne v r) F =
  ⊩τ-⋆◃ τ (▹⋆-trans (▹⋆-cong :pμ₁ r) (▹⋆-cong {f = pμ (back-ne v)} :pμ₂
  (step (:ηλ f) (▹⋆-cong {f = :λ} :λ ([ τ ] _ ▹⋆↑ _)))))
  (↓[ τ ] pμ v (:λ (↑[ τ ] F (step (same Γ)) (↓[ F[ d ] (μ d) ] :v here!) refl)))
vmu τ {f} (:C {._} {t} v r) F =
  F (same _) v (▹⋆-trans (▹⋆-cong :pμ₁ r)
  (step :pμ (coerce (λ f' → :a f t ▹⋆ :a f' t) (sym (weaken-same f)) refl)))

-- join

vtimes : ∀ {Γ d₁ d₂} σ {m} τ {f} (M : Γ ⊩τ F[ d₁ × d₂ ] σ [ m ]) (F : Γ ⊩τ F[ d₁ ] σ ▹ F[ d₂ ] σ ▹ τ [ f ]) →
         Γ ⊩τ τ [ p× m f ]
vtimes {Γ} σ τ {f} (:× {._} {._} {._} {t₁} {t₂} M₁ M₂ r) F =
  F (same _) M₁ (coerce (λ t → (:a t t₁) ▹⋆ (:a (weaken (same Γ) f) t₁)) (weaken-same f) refl)
    (same _) M₂ (▹⋆-trans (▹⋆-cong :p×₁ r) (step :p×
    (coerce₂ (λ f' t₁' → :a (:a f' t₁') t₂ ▹⋆ :a (:a (weaken (same Γ) f) (weaken (same Γ) t₁)) t₂)
    (weaken-same f) (weaken-same t₁) refl)))

-- rec

vhole : ∀ {σ Γ} τ {m f} (M : Γ ⊩τ F[ [] ] σ [ m ]) (F : Γ ⊩τ σ ▹ τ [ f ]) → Γ ⊩τ τ [ p[] m f ]
vhole τ {m} {f} (:r {._} {t} v r) F =
  F (same _) v (▹⋆-trans (▹⋆-cong :p[]₁ r)
  (step :p[] (coerce (λ g → :a g t ▹⋆ :a (weaken (same _) f) t) (weaken-same f) refl)))

-- branch

vplus : ∀ {Γ d₁ d₂} σ {m} τ {f₁ f₂} (M : Γ ⊩τ F[ d₁ + d₂ ] σ [ m ])
        (F₁ : Γ ⊩τ F[ d₁ ] σ ▹ τ [ f₁ ]) (F₂ : Γ ⊩τ F[ d₂ ] σ ▹ τ [ f₂ ]) → Γ ⊩τ τ [ p+ m f₁ f₂ ]
vplus σ τ {f₁} (:+₁ M r) F₁ F₂ =
  F₁ (same _) M (▹⋆-trans (▹⋆-cong :p+₁ r)
  (step :p+l (coerce (λ f → :a f _ ▹⋆ :a (weaken (same _) f₁) _) (weaken-same f₁) refl)))
vplus σ τ {f₁} {f₂} (:+₂ M r) F₁ F₂ =
  F₂ (same _) M (▹⋆-trans (▹⋆-cong :p+₁ r)
  (step :p+r (coerce (λ f → :a f _ ▹⋆ :a (weaken (same _) f₂) _) (weaken-same f₂) refl)))
vplus {Γ} {d₁} {d₂} σ τ {f₁} {f₂} (mF {._} {._} {_} {t} {f} F T r) F₁ F₂ =
  -- cast
  ⊩τ-⋆◃ τ (▹⋆-trans (▹⋆-cong :p+₁ r) (step (p+mF _ _ _) (▹⋆-trans
    (▹⋆-cong {f = λ t → p+ (back-ne T) (:λ t) _} (:p+₂ ∘ :λ) ([ τ ] _ ▹⋆↑ _))
    (▹⋆-cong {f = λ t → p+ (back-ne T) _ (:λ t)} (:p+₃ ∘ :λ) ([ τ ] _ ▹⋆↑ _)))))
  -- actual computation: activating a neutral eliminator application
  (↓[ τ ] p+ T
    -- first branch
    (:λ (↑[ τ ] F₁ (step (same _)) (⊩τ-mF (λ {Δ} inc S →
    coerce (λ g → Δ ⊩τ σ [ :a g (back-ne S) ]) (sym (weaken² (step (same _)) inc f))
    (F (⊆-trans (step (same _)) inc) S)) (:v here!)) refl))
    -- second branch
    (:λ (↑[ τ ] F₂ (step (same _)) (⊩τ-mF (λ {Δ} inc S → 
    coerce (λ g → Δ ⊩τ σ [ :a g (back-ne S) ]) (sym (weaken² (step (same _)) inc f))
    (F (⊆-trans (step (same _)) inc) S)) (:v here!)) refl)))

eval : ∀ {Γ Δ σ} (t : Γ ⊢ σ) (ρ : Δ ⊩ Γ) (vs : Δ ⊩ε Γ [ ρ ]) → Δ ⊩τ σ [ subst t ρ ]
eval (:v pr) ρ vs = lookup _ pr vs
eval {Γ} {Δ} {σ ▹ τ} (:λ t) ρ vs =
  λ {Ε} inc {s} v {ts} r →
  -- β-expansion of the decorative term
  ⊩τ-⋆◃ τ (▹⋆-trans r (step (:β _ _) (coerce (λ t' → t' ▹⋆ subst t (s , ⊩-weaken Γ inc ρ))
  (sym (trans (subst-weaken (pop! inc) (subst t (:v here! , _)) (s , Γ⊩ Ε))
  (trans (subst² t _ (s , purge inc (Γ⊩ Ε))) (cong (λ ρ → subst t (s , ρ))
  (trans (⊩²-step Γ _ _ s) (trans (cong (⊩² Γ ρ) (purge-Γ⊩ inc)) (trans (⊩²-weaken Γ inc _ _)
  (cong (⊩-weaken Γ inc) (⊩²-Γ⊩-r Γ ρ))))))))) refl)))
  -- actual computation
  (eval t (s , ⊩-weaken Γ inc ρ) (v , ⊩ε-weaken Γ inc vs))
eval (:a t u) ρ vs = vapp _ _ (eval t ρ vs) (eval u ρ vs)
eval (:C t) ρ vs = :C (eval t ρ vs) refl
eval :u ρ vs = :u
eval (:r t) ρ vs = :r (eval t ρ vs) refl
eval (:+₁ t) ρ vs = :+₁ (eval t ρ vs) refl
eval (:+₂ t) ρ vs = :+₂ (eval t ρ vs) refl
eval (:× t₁ t₂) ρ vs = :× (eval t₁ ρ vs) (eval t₂ ρ vs) refl
eval (mF t m) ρ vs = vmap _ _ (eval t ρ vs) (eval m ρ vs)
eval (p[] m t) ρ vs = vhole _ (eval m ρ vs) (eval t ρ vs)
eval (p+ m t₁ t₂) ρ vs = vplus _ _ (eval m ρ vs) (eval t₁ ρ vs) (eval t₂ ρ vs)
eval (p× m t) ρ vs = vtimes _ _ (eval m ρ vs) (eval t ρ vs)
eval (pμ m t) ρ vs = vmu _ (eval m ρ vs) (eval t ρ vs)
eval (μμ m t) ρ vs = vrec _ _ (eval m ρ vs) (eval t ρ vs)

{- Quotienting the set of terms by the reduction relations
   amounts to evaluating the term on the trivial environment. -}

quotient : ∀ {Γ σ} (t : Γ ⊢ σ) → Γ ⊩τ σ [ t ]
quotient {Γ} {σ} t = coerce (λ t → Γ ⊩τ σ [ t ]) (subst-Γ⊩ t) (eval t _ (Γ⊩ε Γ))

to-the-future : ∀ {σ Γ} (t : Γ ⊢ σ) → Γ ⊢nf σ
to-the-future {σ} t = ↑[ σ ] (quotient t)

norm : ∀ {Γ σ} (t : Γ ⊢ σ) → Γ ⊢ σ
norm = back-nf ∘ to-the-future

{- The normalization gives you back a reduct of the original
   term which entails that it is sound: two elements which
   have the same normal forms are related. -}

norm-reduces : ∀ {σ Γ} (t : Γ ⊢ σ) → t ▹⋆ norm t
norm-reduces {σ} t = [ σ ] t ▹⋆↑ quotient t

soundness : ∀ {Γ σ} (t u : Γ ⊢ σ) (pr : norm t ≡ norm u) → t ≡βη u
soundness t u pr =
  ≡⋆-trans (▹≡⋆ (norm-reduces t)) (≡⋆-sym (coerce (_≡βη_ u) (sym pr) (▹≡⋆ (norm-reduces u))))