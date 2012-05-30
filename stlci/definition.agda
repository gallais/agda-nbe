module stlci.definition where

open import Data.Unit
open import Data.Product renaming (_×_ to _⊗_)
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'}
        (eqa : a ≡ a') (eqb : b ≡ b') (eqc : c ≡ c') → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

open import tools.contexts

infixr 10 _▹_
infix 10 _⊢_ _⊩_

{- We work here with a lambda-calculus enriched with a
   universe of finitely branching inductive skeletons
   (i.e. no values stored inside the inductive types)
   and their eliminators and recursors. -}

data ind : Set where
-- [stop] and [rec]
  ◾ [] : ind
-- branching and joining
  _+_ _×_ : (d₁ d₂ : ind) → ind

data ty : Set where
-- empty type
  Ø : ty
-- arrow type
  _▹_ : (σ τ : ty) → ty
-- application of a functor to a type
  F[_]_ : (d : ind) (σ : ty) → ty
-- fixpoint of a skeleton description
  μ_ : (d : ind) → ty

data _⊢_ (Γ : Con ty) : ty → Set where
-- usual definitions: variable, λ-abstraction, application, datatype constructor
  :v : {σ : ty} (pr : σ ∈ Γ) → Γ ⊢ σ
  :λ : {σ τ : ty} (t : Γ ∙ σ ⊢ τ) → Γ ⊢ σ ▹ τ
  :a : {σ τ : ty} (t : Γ ⊢ σ ▹ τ) (u : Γ ⊢ σ) → Γ ⊢ τ
  :C : {d : ind} (t : Γ ⊢ F[ d ] (μ d)) → Γ ⊢ μ d
-- How to deal with functors on the goal's side
  :u : {σ : ty} → Γ ⊢ F[ ◾ ] σ
  :r : {σ : ty} (t : Γ ⊢ σ) → Γ ⊢ F[ [] ] σ
  :+₁ : {d₁ d₂ : ind} {σ : ty} (t : Γ ⊢ F[ d₁ ] σ) → Γ ⊢ F[ d₁ + d₂ ] σ
  :+₂ : {d₁ d₂ : ind} {σ : ty} (t : Γ ⊢ F[ d₂ ] σ) → Γ ⊢ F[ d₁ + d₂ ] σ
  :× : {d₁ d₂ : ind} {σ : ty} (t₁ : Γ ⊢ F[ d₁ ] σ) (t₂ : Γ ⊢ F[ d₂ ] σ) → Γ ⊢ F[ d₁ × d₂ ] σ
-- map on functors
  mF : {d : ind} {σ τ : ty} (f : Γ ⊢ σ ▹ τ) (v : Γ ⊢ F[ d ] σ) → Γ ⊢ F[ d ] τ
-- pattern matching
  p[] : {σ τ : ty} (m : Γ ⊢ F[ [] ] σ) (f : Γ ⊢ σ ▹ τ) → Γ ⊢ τ
  p+ : {d₁ d₂ : ind} {σ τ : ty} (m : Γ ⊢ F[ d₁ + d₂ ] σ)
       (f₁ : Γ ⊢ F[ d₁ ] σ ▹ τ) (f₂ : Γ ⊢ F[ d₂ ] σ ▹ τ) → Γ ⊢ τ
  p× : {d₁ d₂ : ind} {σ τ : ty} (m : Γ ⊢ F[ d₁ × d₂ ] σ) (f : Γ ⊢ F[ d₁ ] σ ▹ F[ d₂ ] σ ▹ τ) → Γ ⊢ τ
  pμ : {d : ind} {σ : ty} (m : Γ ⊢ μ d) (f : Γ ⊢ F[ d ] (μ d) ▹ σ) → Γ ⊢ σ
-- induction on an inductive type
  μμ : {d : ind} {σ : ty} (m : Γ ⊢ μ d) (t : Γ ⊢ (F[ d ] σ) ▹ σ) → Γ ⊢ σ

weaken : ∀ {Γ Δ σ} (pr : Γ ⊆ Δ) (t : Γ ⊢ σ) → Δ ⊢ σ
weaken inc (:v pr) = :v (inc-in inc pr)
weaken inc (:λ t) = :λ (weaken (pop! inc) t)
weaken inc (:a t u) = :a (weaken inc t) (weaken inc u)
weaken inc (:C t) = :C (weaken inc t)
weaken inc :u = :u
weaken inc (:r t) = :r (weaken inc t)
weaken inc (:+₁ t) = :+₁ (weaken inc t)
weaken inc (:+₂ t) = :+₂ (weaken inc t)
weaken inc (:× t u) = :× (weaken inc t) (weaken inc u) 
weaken inc (mF f t) = mF (weaken inc f) (weaken inc t)
weaken inc (p[] m t) = p[] (weaken inc m) (weaken inc t)
weaken inc (p+ m t₁ t₂) = p+ (weaken inc m) (weaken inc t₁) (weaken inc t₂)
weaken inc (p× m t) = p× (weaken inc m) (weaken inc t)
weaken inc (pμ m t) = pμ (weaken inc m) (weaken inc t)
weaken inc (μμ m t) = μμ (weaken inc m) (weaken inc t)

{- Definition of context realizers. A context realizer
   [Δ ⊩ Γ] give rise to a substitution function mapping
   terms from [Γ ⊢ A] to [Δ ⊢ A]. -}

_⊩_ : Con ty → Con ty → Set
Δ ⊩ ε = ⊤
Δ ⊩ (Γ ∙ γ) = Δ ⊢ γ ⊗ Δ ⊩ Γ

⊩-weaken : ∀ {Δ Ε} Γ (pr : Δ ⊆ Ε) (ρ : Δ ⊩ Γ) → Ε ⊩ Γ
⊩-weaken ε pr ρ = tt
⊩-weaken (Γ ∙ γ) pr (r , ρ) = weaken pr r , ⊩-weaken Γ pr ρ

-- one can always produce a trivial environment

Γ⊩_ : (Γ : Con ty) → Γ ⊩ Γ
Γ⊩ ε = tt
Γ⊩ (Γ ∙ γ) = :v here! , ⊩-weaken Γ (step (same Γ)) (Γ⊩ Γ)

-- definition of substitution

get : ∀ {Γ Δ σ} (pr : σ ∈ Γ) (ρ : Δ ⊩ Γ) → Δ ⊢ σ
get here! (r , _) = r
get (there pr) (_ , ρ) = get pr ρ

subst : ∀ {Γ Δ σ} (t : Γ ⊢ σ) (ρ : Δ ⊩ Γ) → Δ ⊢ σ
subst (:v pr) ρ = get pr ρ
subst {Γ} {Δ} (:λ t) ρ = :λ (subst t (:v here! , ⊩-weaken Γ (step (same Δ)) ρ))
subst (:a t u) ρ = :a (subst t ρ) (subst u ρ)
subst (:C t) ρ = :C (subst t ρ)
subst :u ρ = :u
subst (:r t) ρ = :r (subst t ρ)
subst (:+₁ t) ρ = :+₁ (subst t ρ)
subst (:+₂ t) ρ = :+₂ (subst t ρ)
subst (:× t₁ t₂) ρ = :× (subst t₁ ρ) (subst t₂ ρ)
subst (mF m t) ρ = mF (subst m ρ) (subst t ρ)
subst (p[] m t) ρ = p[] (subst m ρ) (subst t ρ)
subst (p+ m t₁ t₂) ρ = p+ (subst m ρ) (subst t₁ ρ) (subst t₂ ρ)
subst (p× m t) ρ = p× (subst m ρ) (subst t ρ)
subst (pμ m t) ρ = pμ (subst m ρ) (subst t ρ)
subst (μμ m t) ρ = μμ (subst m ρ) (subst t ρ)

-- simplification and composition of environments

purge : ∀ {Γ Δ Ε} (pr : Γ ⊆ Δ) (ρ : Ε ⊩ Δ) → Ε ⊩ Γ
purge base ρ = ρ
purge (step inc) (_ , ρ) = purge inc ρ
purge (pop! inc) (r , ρ) = r , purge inc ρ

⊩² : ∀ {Δ Ε} Γ (ρ₁ : Δ ⊩ Γ) (ρ₂ : Ε ⊩ Δ) → Ε ⊩ Γ
⊩² ε ρ₁ ρ₂ = tt
⊩² (Γ ∙ γ) (r₁ , ρ₁) ρ₂ = subst r₁ ρ₂ , ⊩² Γ ρ₁ ρ₂

{- We can define operations on terms such as η expansion,
   β-reduction and the different kinds of compositions
   needed for the map-fusions laws. -}

η-expand : ∀ {Γ σ τ} (t : Γ ⊢ σ ▹ τ) → Γ ⊢ σ ▹ τ
η-expand t = :λ (:a (weaken (step (same _)) t) (:v here!))

β-reduce : ∀ {Γ σ τ} (t : Γ ∙ σ ⊢ τ) (s : Γ ⊢ σ) → Γ ⊢ τ
β-reduce {Γ} t s = subst t (s , Γ⊩ Γ)

id : ∀ {Γ σ} → Γ ⊢ σ ▹ σ
id = :λ (:v here!)

_:∘_ : ∀ {Γ σ τ υ} (g : Γ ⊢ τ ▹ υ) (f : Γ ⊢ σ ▹ τ) → Γ ⊢ σ ▹ υ
g :∘ f = :λ (:a (weaken (step (same _)) g) (:a (weaken (step (same _)) f) (:v here!)))

_:∘mF[_] : ∀ {d Γ σ τ υ} (t : Γ ⊢ F[ d ] τ ▹ υ) (f : Γ ⊢ σ ▹ τ) → Γ ⊢ F[ d ] σ ▹ υ
t :∘mF[ f ] = :λ (:a (weaken (step (same _)) t) (mF (weaken (step (same _)) f) (:v here!)))

_:∘mF₂[_] : ∀ {d₁ d₂ Γ σ τ υ} (t : Γ ⊢ F[ d₁ ] τ ▹ F[ d₂ ] τ ▹ υ ) (f : Γ ⊢ σ ▹ τ) →
            Γ ⊢ F[ d₁ ] σ ▹ F[ d₂ ] σ ▹ υ
t :∘mF₂[ f ] =
  :λ (:λ (:a (:a (weaken (step (step (same _))) t)
  (mF (weaken (step (step (same _))) f) (:v (there here!))))
  (mF (weaken (step (step (same _))) f) (:v here!))))

mF[_:∘_] : ∀ {Γ d σ τ υ} (g : Γ ⊢ τ ▹ υ) (f : Γ ⊢ σ ▹ F[ d ] τ) → Γ ⊢ σ ▹ F[ d ] υ
mF[ g :∘ f ] = :λ (mF (weaken (step (same _)) g) (:a (weaken (step (same _)) f) (:v here!)))

mF₂[_:∘_] : ∀ {Γ d σ τ υ ν} (g : Γ ⊢ υ ▹ ν) (f : Γ ⊢ σ ▹ τ ▹ F[ d ] υ) → Γ ⊢ σ ▹ τ ▹ F[ d ] ν
mF₂[ g :∘ f ] =
  :λ (:λ (mF (weaken (step (step (same _))) g)
  (:a (:a (weaken (step (step (same _))) f) (:v (there here!))) (:v here!))))


{- We now have technical lemmas proving that weakening
   commutes with the usual operations on terms. -}

-- terms

weaken-same : ∀ {Γ σ} (t : Γ ⊢ σ) → weaken (same Γ) t ≡ t
weaken-same (:v pr) = cong :v (inc-in-same pr)
weaken-same (:λ t) = cong :λ (weaken-same t)
weaken-same (:a t u) = cong₂ :a (weaken-same t) (weaken-same u)
weaken-same (:C t) = cong :C (weaken-same t)
weaken-same :u = refl
weaken-same (:r t) = cong :r (weaken-same t)
weaken-same (:+₁ t) = cong :+₁ (weaken-same t)
weaken-same (:+₂ t) = cong :+₂ (weaken-same t)
weaken-same (:× t₁ t₂) = cong₂ :× (weaken-same t₁) (weaken-same t₂)
weaken-same (mF m t) = cong₂ mF (weaken-same m) (weaken-same t)
weaken-same (p[] m t) = cong₂ p[] (weaken-same m) (weaken-same t)
weaken-same (p+ m t₁ t₂) = cong₃ p+ (weaken-same m) (weaken-same t₁) (weaken-same t₂)
weaken-same (p× m t) = cong₂ p× (weaken-same m) (weaken-same t)
weaken-same (pμ m t) = cong₂ pμ (weaken-same m) (weaken-same t)
weaken-same (μμ m t) = cong₂ μμ (weaken-same m) (weaken-same t)

weaken² : ∀ {Γ Δ Ε σ} (pr₁ : Γ ⊆ Δ) (pr₂ : Δ ⊆ Ε) (t : Γ ⊢ σ) →
            weaken pr₂ (weaken pr₁ t) ≡ weaken (⊆-trans pr₁ pr₂) t
weaken² pr₁ pr₂ (:v pr) = cong :v (inc-in² pr₁ pr₂ pr)
weaken² pr₁ pr₂ (:λ t) = cong :λ (weaken² (pop! pr₁) (pop! pr₂) t)
weaken² pr₁ pr₂ (:a t u) = cong₂ :a (weaken² pr₁ pr₂ t) (weaken² pr₁ pr₂ u)
weaken² pr₁ pr₂ (:C t) = cong :C (weaken² pr₁ pr₂ t)
weaken² pr₁ pr₂ :u = refl
weaken² pr₁ pr₂ (:r t) = cong :r (weaken² pr₁ pr₂ t)
weaken² pr₁ pr₂ (:+₁ t) = cong :+₁ (weaken² pr₁ pr₂ t)
weaken² pr₁ pr₂ (:+₂ t) = cong :+₂ (weaken² pr₁ pr₂ t)
weaken² pr₁ pr₂ (:× t₁ t₂) = cong₂ :× (weaken² pr₁ pr₂ t₁) (weaken² pr₁ pr₂ t₂)
weaken² pr₁ pr₂ (mF m t) = cong₂ mF (weaken² pr₁ pr₂ m) (weaken² pr₁ pr₂ t)
weaken² pr₁ pr₂ (p[] m t) = cong₂ p[] (weaken² pr₁ pr₂ m) (weaken² pr₁ pr₂ t)
weaken² pr₁ pr₂ (p+ m t₁ t₂) = cong₃ p+ (weaken² pr₁ pr₂ m) (weaken² pr₁ pr₂ t₁) (weaken² pr₁ pr₂ t₂)
weaken² pr₁ pr₂ (p× m t) = cong₂ p× (weaken² pr₁ pr₂ m) (weaken² pr₁ pr₂ t)
weaken² pr₁ pr₂ (pμ m t) = cong₂ pμ (weaken² pr₁ pr₂ m) (weaken² pr₁ pr₂ t)
weaken² pr₁ pr₂ (μμ m t) = cong₂ μμ (weaken² pr₁ pr₂ m) (weaken² pr₁ pr₂ t)

-- environments

⊩-weaken-same : ∀ {Δ} Γ (ρ : Δ ⊩ Γ) → ⊩-weaken Γ (same Δ) ρ ≡ ρ
⊩-weaken-same ε tt = refl
⊩-weaken-same (Γ ∙ _) (r , ρ) = cong₂ _,_ (weaken-same r) (⊩-weaken-same Γ ρ)

⊩-weaken² : ∀ {Δ Ε Ν} Γ (pr₁ : Δ ⊆ Ε) (pr₂ : Ε ⊆ Ν) (ρ : Δ ⊩ Γ) →
            ⊩-weaken Γ pr₂ (⊩-weaken Γ pr₁ ρ) ≡ ⊩-weaken Γ (⊆-trans pr₁ pr₂) ρ
⊩-weaken² ε pr₁ pr₂ ρ = refl
⊩-weaken² (Γ ∙ _) pr₁ pr₂ (r , ρ) = cong₂ _,_ (weaken² pr₁ pr₂ r) (⊩-weaken² Γ pr₁ pr₂ ρ)

get-weaken : ∀ {Γ Δ Ε σ} (pr : σ ∈ Γ) (inc : Δ ⊆ Ε) (ρ : Δ ⊩ Γ) →
             weaken inc (get pr ρ) ≡ get pr (⊩-weaken Γ inc ρ)
get-weaken here! inc ρ = refl
get-weaken (there pr) inc (_ , ρ) = get-weaken pr inc ρ

-- purges

purge-same : ∀ {Δ} Γ (ρ : Δ ⊩ Γ) → purge (same Γ) ρ ≡ ρ
purge-same ε ρ = refl
purge-same (Γ ∙ _) (r , ρ) = cong (λ ρ → r , ρ) (purge-same Γ ρ)

⊩-weaken-purge : ∀ {Γ Δ Ε Ν} (pr₁ : Γ ⊆ Δ) (pr₂ : Ε ⊆ Ν) (ρ : Ε ⊩ Δ) →
                ⊩-weaken Γ pr₂ (purge pr₁ ρ) ≡ purge pr₁ (⊩-weaken Δ pr₂ ρ)
⊩-weaken-purge base pr₂ ρ = refl
⊩-weaken-purge (step inc) pr₂ (_ , ρ) = ⊩-weaken-purge inc pr₂ ρ
⊩-weaken-purge (pop! inc) pr₂ (r , ρ) = cong (_,_ _) (⊩-weaken-purge inc pr₂ ρ)

purge-Γ⊩ : ∀ {Γ Δ} (pr : Γ ⊆ Δ) → purge pr (Γ⊩ Δ) ≡ ⊩-weaken Γ pr (Γ⊩ Γ)
purge-Γ⊩ base = refl
purge-Γ⊩ (step {Γ} {Δ} {σ} pr) =
  trans (sym (⊩-weaken-purge pr (step (same Δ)) (Γ⊩ Δ)))
  (trans (cong (⊩-weaken Γ (step (same Δ))) (purge-Γ⊩ pr))
  (trans (⊩-weaken² Γ pr (step (same Δ)) (Γ⊩ Γ))
  (cong (λ pr → ⊩-weaken Γ pr (Γ⊩ Γ)) (trans (sym (⊆-step-same {ty} {Γ} {Δ} pr))
  (cong step (⊆-same-l pr))))))
purge-Γ⊩ (pop! {Γ} {Δ} {σ} pr) =
  cong (_,_ _) (trans (trans (sym (⊩-weaken-purge pr (step (same Δ)) (Γ⊩ Δ)))
               (trans (cong (⊩-weaken Γ _) (purge-Γ⊩ pr))
               (trans (⊩-weaken² Γ pr (step (same Δ)) (Γ⊩ Γ))
               (cong (λ pr → ⊩-weaken Γ pr (Γ⊩ Γ)) (sym (⊆-step-same {ty} {Γ} {Δ} pr))))))
               (sym (⊩-weaken² Γ (step (same Γ)) (pop! pr) (Γ⊩ Γ))))

-- substitutions

weaken-subst : ∀ {Γ Δ Ε σ} (inc : Δ ⊆ Ε) (t : Γ ⊢ σ) (ρ : Δ ⊩ Γ) →
               weaken inc (subst t ρ) ≡ subst t (⊩-weaken Γ inc ρ)
weaken-subst inc (:v pr) ρ = get-weaken pr inc ρ
weaken-subst {Γ} {Δ} inc (:λ t) ρ = 
  cong :λ (trans (weaken-subst (pop! inc) t (:v here! , ⊩-weaken Γ (step (same Δ)) ρ))
  (cong (λ ρ → subst t (:v here! , ρ)) (trans (⊩-weaken² Γ (step (same Δ)) (pop! inc) ρ)
  (trans (cong (λ pr → ⊩-weaken Γ pr ρ) (⊆-step-same inc))
         (sym (⊩-weaken² Γ inc (step (same _)) ρ))))))
weaken-subst inc (:a t u) ρ = cong₂ :a (weaken-subst inc t ρ) (weaken-subst inc u ρ)
weaken-subst inc (:C t) ρ = cong :C (weaken-subst inc t ρ)
weaken-subst inc :u ρ = refl
weaken-subst inc (:r t) ρ = cong :r (weaken-subst inc t ρ)
weaken-subst inc (:+₁ t) ρ = cong :+₁ (weaken-subst inc t ρ)
weaken-subst inc (:+₂ t) ρ = cong :+₂ (weaken-subst inc t ρ)
weaken-subst inc (:× t₁ t₂) ρ = cong₂ :× (weaken-subst inc t₁ ρ) (weaken-subst inc t₂ ρ)
weaken-subst inc (mF m t) ρ = cong₂ mF (weaken-subst inc m ρ) (weaken-subst inc t ρ)
weaken-subst inc (p[] m t) ρ = cong₂ p[] (weaken-subst inc m ρ) (weaken-subst inc t ρ)
weaken-subst inc (p+ m t₁ t₂) ρ =
  cong₃ p+ (weaken-subst inc m ρ) (weaken-subst inc t₁ ρ) (weaken-subst inc t₂ ρ)
weaken-subst inc (p× m t) ρ = cong₂ p× (weaken-subst inc m ρ) (weaken-subst inc t ρ)
weaken-subst inc (pμ m t) ρ = cong₂ pμ (weaken-subst inc m ρ) (weaken-subst inc t ρ)
weaken-subst inc (μμ m t) ρ = cong₂ μμ (weaken-subst inc m ρ) (weaken-subst inc t ρ)

get-inc : ∀ {Γ Δ Ε σ} (inc : Γ ⊆ Δ) (pr : σ ∈ Γ) (ρ : Ε ⊩ Δ) →
          get (inc-in inc pr) ρ ≡ get pr (purge inc ρ)
get-inc base () _
get-inc (step inc) here! (_ , ρ) = get-inc inc here! ρ
get-inc (pop! inc) here! ρ = refl
get-inc (step inc) (there pr) (_ , ρ) = get-inc inc (there pr) ρ
get-inc (pop! inc) (there pr) (_ , ρ) = get-inc inc pr ρ

subst-weaken : ∀ {Γ Δ Ε σ} (inc : Γ ⊆ Δ) (t : Γ ⊢ σ) (ρ : Ε ⊩ Δ) →
            subst (weaken inc t) ρ ≡ subst t (purge inc ρ)
subst-weaken inc (:v pr) ρ = get-inc inc pr ρ
subst-weaken {Γ} {Δ} inc (:λ t) ρ =
  cong :λ (trans (subst-weaken (pop! inc) t (:v here! , ⊩-weaken Δ (step (same _)) ρ))
  (cong (λ ρ → subst t (:v here! , ρ)) (sym (⊩-weaken-purge inc (step (same _)) ρ))))
subst-weaken inc (:a t u) ρ = cong₂ :a (subst-weaken inc t ρ) (subst-weaken inc u ρ)
subst-weaken inc (:C t) ρ = cong :C (subst-weaken inc t ρ)
subst-weaken inc :u ρ = refl
subst-weaken inc (:r t) ρ = cong :r (subst-weaken inc t ρ)
subst-weaken inc (:+₁ t) ρ = cong :+₁ (subst-weaken inc t ρ)
subst-weaken inc (:+₂ t) ρ = cong :+₂ (subst-weaken inc t ρ)
subst-weaken inc (:× t₁ t₂) ρ = cong₂ :× (subst-weaken inc t₁ ρ) (subst-weaken inc t₂ ρ)
subst-weaken inc (mF m t) ρ = cong₂ mF (subst-weaken inc m ρ) (subst-weaken inc t ρ)
subst-weaken inc (p[] m t) ρ = cong₂ p[] (subst-weaken inc m ρ) (subst-weaken inc t ρ)
subst-weaken inc (p+ m t₁ t₂) ρ =
  cong₃ p+ (subst-weaken inc m ρ) (subst-weaken inc t₁ ρ) (subst-weaken inc t₂ ρ)
subst-weaken inc (p× m t) ρ = cong₂ p× (subst-weaken inc m ρ) (subst-weaken inc t ρ)
subst-weaken inc (pμ m t) ρ = cong₂ pμ (subst-weaken inc m ρ) (subst-weaken inc t ρ)
subst-weaken inc (μμ m t) ρ = cong₂ μμ (subst-weaken inc m ρ) (subst-weaken inc t ρ)

-- η expansions

η-weaken : ∀ {Γ Δ σ τ} (pr : Γ ⊆ Δ) (t : Γ ⊢ σ ▹ τ) →
           weaken pr (η-expand t) ≡ η-expand (weaken pr t)
η-weaken pr t =
  cong (λ t → :λ (:a t (:v here!))) (trans (weaken² _ _ t)
  (trans (cong (λ pr → weaken pr t) (⊆-step-same pr)) (sym (weaken² _ _ t))))

-- β reductions

β-weaken : ∀ {Γ Δ σ τ} (pr : Γ ⊆ Δ) (t : Γ ∙ σ ⊢ τ) (s : Γ ⊢ σ) →
           weaken pr (β-reduce t s) ≡ β-reduce (weaken (pop! pr) t) (weaken pr s)
β-weaken {Γ} {Δ} pr t s =
  trans (weaken-subst pr t (s , Γ⊩ Γ))
  (trans (cong (λ ρ → subst t (weaken pr s , ρ)) (sym (purge-Γ⊩ pr)))
  (sym (subst-weaken (pop! pr) t (weaken pr s , Γ⊩ Δ))))

-- composition

:∘-weaken : ∀ {Γ Δ σ τ υ} (pr : Γ ⊆ Δ) (g : Γ ⊢ τ ▹ υ) (f : Γ ⊢ σ ▹ τ) →
            weaken pr (g :∘ f) ≡ (weaken pr g) :∘ (weaken pr f)
:∘-weaken pr g f =
  cong₂ (λ g f → :λ (:a g (:a f (:v here!))))
  (trans (trans (weaken² _ (pop! pr) g) (cong (λ pr → weaken pr g) (⊆-step-same pr)))
    (sym (weaken² pr _ g)))
  (trans (weaken² _ (pop! pr) f) (trans (cong (λ pr → weaken pr f) (⊆-step-same pr))
    (sym (weaken² pr _ f))))

mFc-weaken : ∀ {Γ Δ d σ τ υ} (pr : Γ ⊆ Δ) (g : Γ ⊢ τ ▹ υ) (f : Γ ⊢ σ ▹ F[ d ] τ) →
            weaken pr (mF[ g :∘ f ]) ≡ mF[ weaken pr g :∘ weaken pr f ]
mFc-weaken pr g f =
  cong₂ (λ g f → :λ (mF g (:a f (:v here!))))
  (trans (weaken² _ (pop! pr) g) (trans (cong (λ pr → weaken pr g) (⊆-step-same pr))
    (sym (weaken² pr _ g))))
  (trans (weaken² _ (pop! pr) f) (trans (cong (λ pr → weaken pr f) (⊆-step-same pr))
    (sym (weaken² pr _ f))))

mF₂c-weaken : ∀ {Γ Δ d σ τ υ ν} (pr : Γ ⊆ Δ) (g : Γ ⊢ υ ▹ ν) (f : Γ ⊢ σ ▹ τ ▹ F[ d ] υ) →
             weaken pr mF₂[ g :∘ f ] ≡ mF₂[ weaken pr g :∘ weaken pr f ]
mF₂c-weaken pr g f =
  cong₂ (λ g f → :λ (:λ (mF g (:a (:a f (:v (there here!))) (:v here!)))))
  (trans (weaken² _ (pop! (pop! pr)) g) (trans (cong (λ pr → weaken pr g) (⊆-step₂-same pr))
    (sym (weaken² pr _ g))))
  (trans (weaken² _ (pop! (pop! pr)) f) (trans (cong (λ pr → weaken pr f) (⊆-step₂-same pr))
    (sym (weaken² pr _ f))))

cmF-weaken : ∀ {Γ Δ d σ τ υ} (pr : Γ ⊆ Δ) (g : Γ ⊢ F[ d ] τ ▹ υ) (f : Γ ⊢ σ ▹ τ) →
             weaken pr (g :∘mF[ f ]) ≡ weaken pr g :∘mF[ weaken pr f ]
cmF-weaken pr g f =
  cong₂ (λ g f → :λ (:a g (mF f (:v here!))))
  (trans (weaken² _ (pop! pr) g) (trans (cong (λ pr → weaken pr g) (⊆-step-same pr))
  (sym (weaken² pr _ g))))
  (trans (weaken² _ (pop! pr) f) (trans (cong (λ pr → weaken pr f) (⊆-step-same pr))
  (sym (weaken² pr _ f))))

cmF₂-weaken : ∀ {Γ Δ d₁ d₂ σ τ υ} (pr : Γ ⊆ Δ) (g : Γ ⊢ F[ d₁ ] τ ▹ F[ d₂ ] τ ▹ υ)
              (f : Γ ⊢ σ ▹ τ) → weaken pr (g :∘mF₂[ f ]) ≡ weaken pr g :∘mF₂[ weaken pr f ]
cmF₂-weaken pr g f =
  cong₂ (λ g f → :λ (:λ (:a (:a g (mF f (:v (there here!)))) (mF f (:v here!)))))
  (trans (weaken² _ (pop! (pop! pr)) g) (trans (cong (λ pr → weaken pr g) (⊆-step₂-same pr))
  (sym (weaken² pr _ g))))
  (trans (weaken² _ (pop! (pop! pr)) f) (trans (cong (λ pr → weaken pr f) (⊆-step₂-same pr))
  (sym (weaken² pr _ f))))

-- properties of composition of environments

⊩²-weaken : ∀ {Δ Ε Ν} Γ (pr : Ε ⊆ Ν) (ρ₁ : Δ ⊩ Γ) (ρ₂ : Ε ⊩ Δ) →
                ⊩² Γ ρ₁ (⊩-weaken Δ pr ρ₂) ≡ ⊩-weaken Γ pr (⊩² Γ ρ₁ ρ₂)
⊩²-weaken ε pr ρ₁ ρ₂ = refl
⊩²-weaken (Γ ∙ γ) pr (r₁ , ρ₁) ρ₂ = cong₂ _,_ (sym (weaken-subst pr r₁ ρ₂)) (⊩²-weaken Γ pr ρ₁ ρ₂)

get-⊩² : ∀ {Γ Δ Ε σ} (pr : σ ∈ Γ) (ρ₁ : Δ ⊩ Γ) (ρ₂ : Ε ⊩ Δ) →
           subst (get pr ρ₁) ρ₂ ≡ get pr (⊩² Γ ρ₁ ρ₂)
get-⊩² here! ρ₁ ρ₂ = refl
get-⊩² (there pr) (_ , ρ₁) ρ₂ = get-⊩² pr ρ₁ ρ₂

⊩²-step : ∀ {Δ Ε σ} Γ (ρ₁ : Δ ⊩ Γ) (ρ₂ : Ε ⊩ Δ) (s : Ε ⊢ σ) →
           ⊩² Γ (⊩-weaken Γ (step (same Δ)) ρ₁) (s , ρ₂) ≡ ⊩² Γ ρ₁ ρ₂
⊩²-step ε ρ₁ ρ₂ s = refl
⊩²-step {Δ} (Γ ∙ γ) (r₁ , ρ₁) ρ₂ s = cong₂ _,_
  (trans (subst-weaken (step (same Δ)) r₁ (s , ρ₂)) (cong (subst r₁) (purge-same Δ ρ₂)))
  (⊩²-step Γ ρ₁ ρ₂ s)

-- get from the trivial environment

getΓ⊩-weaken : ∀ {Γ Δ σ} (pr : σ ∈ Γ) (inc : Γ ⊆ Δ) →
               get pr (⊩-weaken Γ inc (Γ⊩ Γ)) ≡ :v (inc-in inc pr)
getΓ⊩-weaken {ε} () inc
getΓ⊩-weaken {Γ ∙ γ} here! inc = refl
getΓ⊩-weaken {Γ ∙ γ} (there pr) inc =
  trans (cong (get pr) (⊩-weaken² Γ (step (same Γ)) inc (Γ⊩ Γ)))
  (trans (getΓ⊩-weaken pr (⊆-trans (step (same _)) inc)) (cong :v (inc-in-step inc pr)))

getΓ⊩ : ∀ {σ Γ} (pr : σ ∈ Γ) → get pr (Γ⊩ Γ) ≡ :v pr
getΓ⊩ here! = refl
getΓ⊩ (there pr) = trans (getΓ⊩-weaken pr (step (same _)))
                         (cong (λ pr → :v (there pr)) (inc-in-same pr))

subst-Γ⊩ : ∀ {Γ σ} (t : Γ ⊢ σ) → subst t (Γ⊩ Γ) ≡ t
subst-Γ⊩ (:v pr) = getΓ⊩ pr
subst-Γ⊩ (:λ t) = cong :λ (subst-Γ⊩ t)
subst-Γ⊩ (:a t u) = cong₂ :a (subst-Γ⊩ t) (subst-Γ⊩ u)
subst-Γ⊩ (:C t) = cong :C (subst-Γ⊩ t)
subst-Γ⊩ :u = refl
subst-Γ⊩ (:r t) = cong :r (subst-Γ⊩ t)
subst-Γ⊩ (:+₁ t) = cong :+₁ (subst-Γ⊩ t)
subst-Γ⊩ (:+₂ t) = cong :+₂ (subst-Γ⊩ t)
subst-Γ⊩ (:× t₁ t₂) = cong₂ :× (subst-Γ⊩ t₁) (subst-Γ⊩ t₂)
subst-Γ⊩ (mF m t) = cong₂ mF (subst-Γ⊩ m) (subst-Γ⊩ t)
subst-Γ⊩ (p[] m t) = cong₂ p[] (subst-Γ⊩ m) (subst-Γ⊩ t)
subst-Γ⊩ (p+ m t₁ t₂) = cong₃ p+ (subst-Γ⊩ m) (subst-Γ⊩ t₁) (subst-Γ⊩ t₂)
subst-Γ⊩ (p× m t) = cong₂ p× (subst-Γ⊩ m) (subst-Γ⊩ t)
subst-Γ⊩ (pμ m t) = cong₂ pμ (subst-Γ⊩ m) (subst-Γ⊩ t)
subst-Γ⊩ (μμ m t) = cong₂ μμ (subst-Γ⊩ m) (subst-Γ⊩ t)

⊩²-Γ⊩-l : ∀ {Δ} Γ (ρ : Δ ⊩ Γ) → ⊩² Γ (Γ⊩ Γ) ρ ≡ ρ
⊩²-Γ⊩-l ε tt = refl
⊩²-Γ⊩-l {Δ} (Γ ∙ γ) (r , ρ) = cong (_,_ r) (trans (⊩²-step Γ (Γ⊩ Γ) ρ r) (⊩²-Γ⊩-l Γ ρ))

⊩²-Γ⊩-r : ∀ {Δ} Γ (ρ : Δ ⊩ Γ) → ⊩² Γ ρ (Γ⊩ Δ) ≡ ρ
⊩²-Γ⊩-r ε tt = refl
⊩²-Γ⊩-r (Γ ∙ γ) (r , ρ) = cong₂ _,_ (subst-Γ⊩ r) (⊩²-Γ⊩-r Γ ρ)

-- η-expansion & substitution

η-subst : ∀ {Γ Δ σ τ} (t : Γ ⊢ σ ▹ τ) (ρ : Δ ⊩ Γ) → subst (η-expand t) ρ ≡ η-expand (subst t ρ)
η-subst {Γ} {Δ} t ρ =
  cong (λ t → :λ (:a t (:v here!))) (trans (subst-weaken _ t _)
  (trans (cong (subst t) (purge-same Γ _)) (sym (weaken-subst _ t ρ))))

-- composition of substitutions

subst² : ∀ {Γ Δ Ε σ} (t : Γ ⊢ σ) (ρ₁ : Δ ⊩ Γ) (ρ₂ : Ε ⊩ Δ) →
             subst (subst t ρ₁) ρ₂ ≡ subst t (⊩² Γ ρ₁ ρ₂)
subst² (:v pr) ρ₁ ρ₂ = get-⊩² pr ρ₁ ρ₂
subst² {Γ} {Δ} {Ε} (:λ t) ρ₁ ρ₂ =
  cong :λ (trans (subst² t _ _) (cong (λ ρ → subst t (:v here! , ρ))
  (trans (⊩²-step Γ ρ₁ _ (:v here!)) (⊩²-weaken Γ (step (same Ε)) ρ₁ ρ₂))))
subst² (:a t u) ρ₁ ρ₂ = cong₂ :a (subst² t ρ₁ ρ₂) (subst² u ρ₁ ρ₂)
subst² (:C t) ρ₁ ρ₂ = cong :C (subst² t ρ₁ ρ₂)
subst² :u ρ₁ ρ₂ = refl
subst² (:r t) ρ₁ ρ₂ = cong :r (subst² t ρ₁ ρ₂)
subst² (:+₁ t) ρ₁ ρ₂ = cong :+₁ (subst² t ρ₁ ρ₂)
subst² (:+₂ t) ρ₁ ρ₂ = cong :+₂ (subst² t ρ₁ ρ₂)
subst² (:× t₁ t₂) ρ₁ ρ₂ = cong₂ :× (subst² t₁ ρ₁ ρ₂) (subst² t₂ ρ₁ ρ₂)
subst² (mF m t) ρ₁ ρ₂ = cong₂ mF (subst² m ρ₁ ρ₂) (subst² t ρ₁ ρ₂)
subst² (p[] m t) ρ₁ ρ₂ = cong₂ p[] (subst² m ρ₁ ρ₂) (subst² t ρ₁ ρ₂)
subst² (p+ m t₁ t₂) ρ₁ ρ₂ = cong₃ p+ (subst² m ρ₁ ρ₂) (subst² t₁ ρ₁ ρ₂) (subst² t₂ ρ₁ ρ₂)
subst² (p× m t) ρ₁ ρ₂ = cong₂ p× (subst² m ρ₁ ρ₂) (subst² t ρ₁ ρ₂)
subst² (pμ m t) ρ₁ ρ₂ = cong₂ pμ (subst² m ρ₁ ρ₂) (subst² t ρ₁ ρ₂)
subst² (μμ m t) ρ₁ ρ₂ = cong₂ μμ (subst² m ρ₁ ρ₂) (subst² t ρ₁ ρ₂)

substβ : ∀ {Γ Δ σ τ} (t : (Γ ∙ σ) ⊢ τ) (s : Γ ⊢ σ) (ρ : Δ ⊩ Γ) →
         subst (β-reduce t s) ρ ≡ subst t (subst s ρ , ρ)
substβ {Γ} {Δ} t s ρ =
  trans (subst² t (s , Γ⊩ Γ) ρ) (cong (λ ρ' → subst t (subst s ρ , ρ')) (⊩²-Γ⊩-l Γ ρ))

βsubst : ∀ {Γ Δ σ τ} (t : (Γ ∙ σ) ⊢ τ) (s : Δ ⊢ σ) (ρ : Δ ⊩ Γ) →
         β-reduce (subst t (:v here! , ⊩-weaken Γ (step (same Δ)) ρ)) s ≡ subst t (s , ρ)
βsubst {Γ} {Δ} t s ρ =
  trans (subst² t (:v here! , ⊩-weaken Γ (step (same Δ)) ρ) (s , Γ⊩ Δ))
        (cong (λ ρ' → subst t (s , ρ')) (trans (⊩²-step Γ ρ (Γ⊩ Δ) s) (⊩²-Γ⊩-r Γ ρ)))

subst-pop : ∀ {Δ Γ σ τ} (t : Γ ⊢ σ) (s : Δ ⊢ τ) (inc : Γ ⊆ Δ) →
            weaken inc t ≡ subst (weaken (pop! inc) (weaken (step (same _)) t)) (s , Γ⊩ Δ)
subst-pop {Δ} t s inc =
  trans (trans (trans (sym (subst-Γ⊩ (weaken inc t))) (trans (subst-weaken inc t (Γ⊩ Δ))
  (cong (λ pr → subst t (purge pr (Γ⊩ Δ))) (sym (⊆-same-l inc)))))
  (sym (subst-weaken (⊆-trans (step (same _)) (pop! inc)) t (s , Γ⊩ Δ))))
  (cong (λ t → subst t (s , Γ⊩ Δ)) (sym (weaken² (step (same _)) (pop! inc) t)))
