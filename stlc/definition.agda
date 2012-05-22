module stlc.definition where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

open import tools.contexts

infix 50 _▹_
infix 10 _⊢_ _⊩_

{- types, terms and environments -}

data ty : Set where
  ♭ : ty
  _▹_ : (σ τ : ty) → ty

data _⊢_ (Γ : Con ty) : ty → Set where
  var : ∀ {σ} (pr : σ ∈ Γ) → Γ ⊢ σ
  lam : ∀ {σ τ} (t : Γ ∙ σ ⊢ τ) → Γ ⊢ σ ▹ τ
  app : ∀ {σ τ} (f : Γ ⊢ σ ▹ τ) (x : Γ ⊢ σ) → Γ ⊢ τ

weaken : ∀ {Γ Δ σ} (pr : Γ ⊆ Δ) (t : Γ ⊢ σ) → Δ ⊢ σ
weaken inc (var pr) = var (inc-in inc pr)
weaken inc (lam t) = lam (weaken (pop! inc) t)
weaken inc (app f x) = app (weaken inc f) (weaken inc x)

_⊩_ : Con ty → Con ty → Set
Δ ⊩ ε = ⊤
Δ ⊩ (Γ ∙ γ) = Δ ⊢ γ × Δ ⊩ Γ

⊩-weaken : ∀ {Δ Ε} Γ (pr : Δ ⊆ Ε) (ρ : Δ ⊩ Γ) → Ε ⊩ Γ
⊩-weaken ε pr ρ = tt
⊩-weaken (Γ ∙ γ) pr (r , ρ) = weaken pr r , ⊩-weaken Γ pr ρ

-- one can always produce a trivial environment

Γ⊩_ : (Γ : Con ty) → Γ ⊩ Γ
Γ⊩ ε = tt
Γ⊩ (Γ ∙ γ) = var here! , ⊩-weaken Γ (step (same Γ)) (Γ⊩ Γ)

{- definition of substitution -}

get : ∀ {Γ Δ σ} (pr : σ ∈ Γ) (ρ : Δ ⊩ Γ) → Δ ⊢ σ
get here! (r , _) = r
get (there pr) (_ , ρ) = get pr ρ

subst : ∀ {Γ Δ σ} (t : Γ ⊢ σ) (ρ : Δ ⊩ Γ) → Δ ⊢ σ
subst (var pr) ρ = get pr ρ
subst {Γ} (lam t) ρ = lam (subst t (var here! , ⊩-weaken Γ (step (same _)) ρ))
subst (app f x) ρ = app (subst f ρ) (subst x ρ)

{- simplification and composition of environments -}

purge : ∀ {Γ Δ Ε} (pr : Γ ⊆ Δ) (ρ : Ε ⊩ Δ) → Ε ⊩ Γ
purge base ρ = ρ
purge (step inc) (_ , ρ) = purge inc ρ
purge (pop! inc) (r , ρ) = r , purge inc ρ

⊩² : ∀ {Δ Ε} Γ (ρ₁ : Δ ⊩ Γ) (ρ₂ : Ε ⊩ Δ) → Ε ⊩ Γ
⊩² ε ρ₁ ρ₂ = tt
⊩² (Γ ∙ γ) (r₁ , ρ₁) ρ₂ = subst r₁ ρ₂ , ⊩² Γ ρ₁ ρ₂

{- definition of η expansion and β-reduction -}

η-expand : ∀ {Γ σ τ} (t : Γ ⊢ σ ▹ τ) → Γ ⊢ σ ▹ τ
η-expand t = lam (app (weaken (step (same _)) t) (var here!))

β-reduce : ∀ {Γ σ τ} (t : Γ ∙ σ ⊢ τ) (s : Γ ⊢ σ) → Γ ⊢ τ
β-reduce {Γ} t s = subst t (s , Γ⊩ Γ)


{--------------------------------------------------}
{---------------- Inversion lemmas ----------------}
{--------------------------------------------------}


var-eq : ∀ {Γ σ} {pr₁ pr₂ : σ ∈ Γ} (h : var pr₁ ≡ var pr₂) → pr₁ ≡ pr₂
var-eq refl = refl 

lam-eq : ∀ {Γ σ τ} {s t : Γ ∙ σ ⊢ τ} → lam s ≡ lam t → s ≡ t
lam-eq refl = refl

appl-eq : ∀ {Γ σ τ} {s t : Γ ⊢ σ ▹ τ} {u v : Γ ⊢ σ} → app s u ≡ app t v → s ≡ t
appl-eq refl = refl

appr-eq : ∀ {Γ σ τ} {s t : Γ ⊢ σ ▹ τ} {u v : Γ ⊢ σ} → app s u ≡ app t v → u ≡ v
appr-eq refl = refl

var-w : ∀ {Γ Δ σ} {inc : Γ ⊆ Δ} (s : Γ ⊢ σ) {t : σ ∈ Δ}
        (Heq : var t ≡ weaken inc s) → Σ (σ ∈ Γ) (λ acc → s ≡ var acc)
var-w (var pr) Heq = pr , refl
var-w (lam t) ()
var-w (app t u) ()

lam-w : ∀ {Γ Δ σ τ} {inc : Γ ⊆ Δ} (s : Γ ⊢ σ ▹ τ) {t : Δ ∙ σ ⊢ τ}
        (Heq : lam t ≡ weaken inc s) → Σ (Γ ∙ σ ⊢ τ) (λ t → s ≡ lam t)
lam-w (var pr) ()
lam-w (lam s) Heq = s , refl
lam-w (app t u) ()

app-w : ∀ {Γ Δ σ τ} {inc : Γ ⊆ Δ} (s : Γ ⊢ τ) {t : Δ ⊢ σ ▹ τ} {u : Δ ⊢ σ}
        (Heq : app t u ≡ weaken inc s) → Σ (Γ ⊢ σ ▹ τ) (λ t → Σ (Γ ⊢ σ) (λ u → s ≡ app t u))
app-w (var pr) ()
app-w (lam t) ()
app-w (app t u) refl = t , u , refl


{--------------------------------------------------}
{------------------- Weakenings -------------------}
{--------------------------------------------------}


-- terms

weaken-same : ∀ {Γ σ} (t : Γ ⊢ σ) → weaken (same Γ) t ≡ t
weaken-same (var pr) = cong var (inc-in-same pr)
weaken-same (lam t) = cong lam (weaken-same t)
weaken-same (app f x) = cong₂ app (weaken-same f) (weaken-same x)

weaken² : ∀ {Γ Δ Ε σ} (pr₁ : Γ ⊆ Δ) (pr₂ : Δ ⊆ Ε) (t : Γ ⊢ σ) →
            weaken pr₂ (weaken pr₁ t) ≡ weaken (⊆-trans pr₁ pr₂) t
weaken² pr₁ pr₂ (var pr) = cong var (inc-in² pr₁ pr₂ pr)
weaken² pr₁ pr₂ (lam t) = cong lam (weaken² (pop! pr₁) (pop! pr₂) t)
weaken² pr₁ pr₂ (app f x) = cong₂ app (weaken² pr₁ pr₂ f) (weaken² pr₁ pr₂ x)

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

weaken-subst : ∀ {Γ Δ Ε σ} (pr : Δ ⊆ Ε) (t : Γ ⊢ σ) (ρ : Δ ⊩ Γ) →
               weaken pr (subst t ρ) ≡ subst t (⊩-weaken Γ pr ρ)
weaken-subst pr (var pr') ρ = get-weaken pr' pr ρ
weaken-subst {Γ} {Δ} pr (lam t) ρ =
  cong lam (trans (weaken-subst (pop! pr) t (var here! , ⊩-weaken Γ (step (same Δ)) ρ))
  (cong (λ ρ → subst t (var here! , ρ)) (trans (⊩-weaken² Γ (step (same Δ)) (pop! pr) ρ)
  (trans (cong (λ pr → ⊩-weaken Γ pr ρ) (⊆-step-same pr)) (sym (⊩-weaken² Γ pr (step (same _)) ρ))))))
weaken-subst pr (app f x) ρ = cong₂ app (weaken-subst pr f ρ) (weaken-subst pr x ρ)

get-inc : ∀ {Γ Δ Ε σ} (inc : Γ ⊆ Δ) (pr : σ ∈ Γ) (ρ : Ε ⊩ Δ) →
          get (inc-in inc pr) ρ ≡ get pr (purge inc ρ)
get-inc base () _
get-inc (step inc) here! (_ , ρ) = get-inc inc here! ρ
get-inc (pop! inc) here! ρ = refl
get-inc (step inc) (there pr) (_ , ρ) = get-inc inc (there pr) ρ
get-inc (pop! inc) (there pr) (_ , ρ) = get-inc inc pr ρ

subst-weaken : ∀ {Γ Δ Ε σ} (pr : Γ ⊆ Δ) (t : Γ ⊢ σ) (ρ : Ε ⊩ Δ) →
            subst (weaken pr t) ρ ≡ subst t (purge pr ρ)
subst-weaken pr (var pr') ρ = get-inc pr pr' ρ
subst-weaken {Γ} {Δ} pr (lam t) ρ =
  cong lam (trans (subst-weaken (pop! pr) t (var here! , ⊩-weaken Δ (step (same _)) ρ))
  (cong (λ ρ → subst t (var here! , ρ)) (sym (⊩-weaken-purge pr (step (same _)) ρ))))
subst-weaken pr (app f x) ρ = cong₂ app (subst-weaken pr f ρ) (subst-weaken pr x ρ)

-- η expansions

η-weaken : ∀ {Γ Δ σ τ} (pr : Γ ⊆ Δ) (t : Γ ⊢ σ ▹ τ) →
           weaken pr (η-expand t) ≡ η-expand (weaken pr t)
η-weaken pr t = cong (λ t → lam (app t (var here!))) (
                trans (weaken² (step (same _)) (pop! pr) t) (
                trans (cong (λ pr → weaken pr t) (⊆-step-same pr)) (
                sym (weaken² pr (step (same _)) t))))

-- β reductions

β-weaken : ∀ {Γ Δ σ τ} (pr : Γ ⊆ Δ) (t : Γ ∙ σ ⊢ τ) (s : Γ ⊢ σ) →
           weaken pr (β-reduce t s) ≡ β-reduce (weaken (pop! pr) t) (weaken pr s)
β-weaken {Γ} {Δ} pr t s =
  trans (weaken-subst pr t (s , Γ⊩ Γ))
        (trans (cong (λ ρ → subst t (weaken pr s , ρ)) (sym (purge-Γ⊩ pr)))
               (sym (subst-weaken (pop! pr) t (weaken pr s , Γ⊩ Δ))))

{- properties of composition of environments -}

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

{- get from the trivial environment -}

getΓ⊩-weaken : ∀ {Γ Δ σ} (pr : σ ∈ Γ) (inc : Γ ⊆ Δ) →
               get pr (⊩-weaken Γ inc (Γ⊩ Γ)) ≡ var (inc-in inc pr)
getΓ⊩-weaken {ε} () inc
getΓ⊩-weaken {Γ ∙ γ} here! inc = refl
getΓ⊩-weaken {Γ ∙ γ} (there pr) inc =
  trans (cong (get pr) (⊩-weaken² Γ (step (same Γ)) inc (Γ⊩ Γ)))
  (trans (getΓ⊩-weaken pr (⊆-trans (step (same _)) inc)) (cong var (inc-in-step inc pr)))

getΓ⊩ : ∀ {σ Γ} (pr : σ ∈ Γ) → get pr (Γ⊩ Γ) ≡ var pr
getΓ⊩ here! = refl
getΓ⊩ (there pr) = trans (getΓ⊩-weaken pr (step (same _)))
                         (cong (λ pr → var (there pr)) (inc-in-same pr))

subst-Γ⊩ : ∀ {Γ σ} (t : Γ ⊢ σ) → subst t (Γ⊩ Γ) ≡ t
subst-Γ⊩ {Γ} (var pr) = getΓ⊩ pr
subst-Γ⊩ (lam t) = cong lam (subst-Γ⊩ t)
subst-Γ⊩ (app f x) = cong₂ app (subst-Γ⊩ f) (subst-Γ⊩ x)

⊩²-Γ⊩-l : ∀ {Δ} Γ (ρ : Δ ⊩ Γ) → ⊩² Γ (Γ⊩ Γ) ρ ≡ ρ
⊩²-Γ⊩-l ε tt = refl
⊩²-Γ⊩-l {Δ} (Γ ∙ γ) (r , ρ) = cong (_,_ r) (trans (⊩²-step Γ (Γ⊩ Γ) ρ r) (⊩²-Γ⊩-l Γ ρ))

⊩²-Γ⊩-r : ∀ {Δ} Γ (ρ : Δ ⊩ Γ) → ⊩² Γ ρ (Γ⊩ Δ) ≡ ρ
⊩²-Γ⊩-r ε tt = refl
⊩²-Γ⊩-r (Γ ∙ γ) (r , ρ) = cong₂ _,_ (subst-Γ⊩ r) (⊩²-Γ⊩-r Γ ρ)

-- η-expansion & substitution

η-subst : ∀ {Γ Δ σ τ} (t : Γ ⊢ σ ▹ τ) (ρ : Δ ⊩ Γ) → subst (η-expand t) ρ ≡ η-expand (subst t ρ)
η-subst {Γ} {Δ} t ρ =
   cong (λ t → lam (app t (var here!)))
   (trans (subst-weaken (step (same Γ)) t (var here! , ⊩-weaken Γ (step (same Δ)) ρ))
   (trans (cong (subst t) (purge-same Γ (⊩-weaken Γ (step (same Δ)) ρ)))
   (sym (weaken-subst (step (same _)) t ρ))))

-- composition of subsitutions

subst² : ∀ {Γ Δ Ε σ} (t : Γ ⊢ σ) (ρ₁ : Δ ⊩ Γ) (ρ₂ : Ε ⊩ Δ) →
             subst (subst t ρ₁) ρ₂ ≡ subst t (⊩² Γ ρ₁ ρ₂)
subst² (var pr) ρ₁ ρ₂ = get-⊩² pr ρ₁ ρ₂
subst² {Γ} {Δ} {Ε} (lam t) ρ₁ ρ₂ =
  cong lam (trans (subst² t _ _) (cong (λ ρ → subst t (var here! , ρ))
  (trans (⊩²-step Γ ρ₁ (⊩-weaken Δ (step (same Ε)) ρ₂) (var here!))
         (⊩²-weaken Γ (step (same Ε)) ρ₁ ρ₂))))
subst² (app f x) ρ₁ ρ₂ = cong₂ app (subst² f ρ₁ ρ₂) (subst² x ρ₁ ρ₂)

substβ : ∀ {Γ Δ σ τ} (t : (Γ ∙ σ) ⊢ τ) (s : Γ ⊢ σ) (ρ : Δ ⊩ Γ) →
         subst (β-reduce t s) ρ ≡ subst t (subst s ρ , ρ)
substβ {Γ} {Δ} t s ρ =
  trans (subst² t (s , Γ⊩ Γ) ρ) (cong (λ ρ' → subst t (subst s ρ , ρ')) (⊩²-Γ⊩-l Γ ρ))

βsubst : ∀ {Γ Δ σ τ} (t : (Γ ∙ σ) ⊢ τ) (s : Δ ⊢ σ) (ρ : Δ ⊩ Γ) →
         β-reduce (subst t (var here! , ⊩-weaken Γ (step (same Δ)) ρ)) s ≡ subst t (s , ρ)
βsubst {Γ} {Δ} t s ρ =
  trans (subst² t (var here! , ⊩-weaken Γ (step (same Δ)) ρ) (s , Γ⊩ Δ))
        (cong (λ ρ' → subst t (s , ρ')) (trans (⊩²-step Γ ρ (Γ⊩ Δ) s) (⊩²-Γ⊩-r Γ ρ)))