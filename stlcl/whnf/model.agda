module stlcl.whnf.model where

open import Data.Unit
open import Data.Sum
open import Data.Product

open import tools.contexts
open import stlcl.definition
open import stlcl.normalforms

infix 10 _⊩_

data _⊩list_by_ {n} (Γ : Con (ty n)) σ (Σ : Con (ty n) → Set) : Set where
  `[]   : Γ ⊩list σ by Σ
  _`∷_  : ∀ (HD : Σ Γ) (TL : Γ ⊢ `list σ × (Γ ⊢whne `list σ ⊎ Γ ⊢whnf `list σ × Γ ⊩list σ by Σ)) →
          Γ ⊩list σ by Σ

mutual

  _⊩'_ : ∀ {n} → Con (ty n) → ty n → Set
  Γ ⊩' `1 = ⊤
  Γ ⊩' `b k = Γ ⊢whne `b k
  Γ ⊩' σ `× τ = Γ ⊩ σ × Γ ⊩ τ
  Γ ⊩' σ `→ τ = ∀ {Δ} (inc : Γ ⊆ Δ) → Δ ⊩ σ → Δ ⊩ τ
  Γ ⊩' `list σ = Γ ⊩list σ by λ Δ → Δ ⊩ σ

  _⊩_ : ∀ {n} → Con (ty n) → ty n → Set
  Γ ⊩ σ = Γ ⊢ σ × (Γ ⊢whne σ ⊎ Γ ⊢whnf σ × Γ ⊩' σ)

weaken-⊩list : ∀ {n} {Γ Δ} {σ : ty n} {Σ} (inc : Γ ⊆ Δ) (weaken-Σ : Σ Γ → Σ Δ) →
  Γ ⊩list σ by Σ → Δ ⊩list σ by Σ
weaken-⊩list inc weaken-Σ `[] = `[]
weaken-⊩list inc weaken-Σ (HD `∷ (tl , inj₁ TL)) =
  weaken-Σ HD `∷
  (⊢-weaken inc tl , inj₁ (weaken-whne inc TL))
weaken-⊩list inc weaken-Σ (HD `∷ (tl₁ , inj₂ (tl₂ , TL))) =
  weaken-Σ HD `∷
  (⊢-weaken inc tl₁ , inj₂ (weaken-whnf inc tl₂ , weaken-⊩list inc weaken-Σ TL))

mutual

  weaken-⊩' : ∀ {n} (σ : ty n) {Γ Δ} (inc : Γ ⊆ Δ) (T : Γ ⊩' σ) → Δ ⊩' σ
  weaken-⊩' `1 inc T = T
  weaken-⊩' (`b k) inc t = weaken-whne inc t
  weaken-⊩' (σ `× τ) inc (A , B) = weaken-⊩ inc A , weaken-⊩ inc B
  weaken-⊩' (σ `→ τ) inc F = λ inc' S → F (⊆-trans inc inc') S
  weaken-⊩' (`list σ) inc XS = weaken-⊩list inc (weaken-⊩ {σ = σ} inc) XS

  weaken-⊩ : ∀ {n} {σ : ty n} {Γ Δ} (inc : Γ ⊆ Δ) (T : Γ ⊩ σ) → Δ ⊩ σ
  weaken-⊩ inc (t , inj₁ T) =
    ⊢-weaken inc t , inj₁ (weaken-whne inc T)
  weaken-⊩ {σ = σ} inc (t₁ , inj₂ (t₂ , T)) =
    ⊢-weaken inc t₁ , inj₂ (weaken-whnf inc t₂ , weaken-⊩' σ inc T)

↑[_]_ : ∀ {n Γ} (σ : ty n) (T : Γ ⊩ σ) → Γ ⊢whnf σ
↑[ σ ] (t , inj₁ T) = `↑ T
↑[ σ ] (t , inj₂ T) = proj₁ T

↓[_]_ : ∀ {n Γ} (σ : ty n) (t : Γ ⊢whne σ) → Γ ⊩ σ
↓[ σ ] t = back-whne t , inj₁ t

_⊩ε_ : ∀ {n} (Δ Γ : Con (ty n)) → Set
Δ ⊩ε ε = ⊤
Δ ⊩ε Γ ∙ σ = Δ ⊩ε Γ × Δ ⊩ σ

weaken-⊩ε : ∀ {n} Γ {Δ Ε : Con (ty n)} (inc : Δ ⊆ Ε) (ρ : Δ ⊩ε Γ) → Ε ⊩ε Γ
weaken-⊩ε ε inc ρ = ρ
weaken-⊩ε (Γ ∙ σ) inc (ρ , r) = weaken-⊩ε Γ inc ρ , weaken-⊩ inc r

Γ⊩ε_ : ∀ {n} (Γ : Con (ty n)) → Γ ⊩ε Γ
Γ⊩ε ε = tt
Γ⊩ε Γ ∙ σ = weaken-⊩ε Γ (step (same _)) (Γ⊩ε Γ) , ↓[ σ ] `v here!

pull : ∀ {n Δ} (Γ : Con (ty n)) → Δ ⊩ε Γ → Δ ⊢ε Γ
pull ε ρ = ρ
pull (Γ ∙ σ) (ρ , (r , _)) = pull Γ ρ , r

infixl 3 _`$'_ _`∷'_
infixr 3 _`++'_ _`,'_ 

_`$'_ : ∀ {n Γ} {σ τ : ty n} (F : Γ ⊩ σ `→ τ) (X : Γ ⊩ σ) → Γ ⊩ τ
f , inj₁ F `$' x , X = f `$ x , inj₁ (F `$ x)
f₁ , inj₂ (f₂ , F) `$' x , X = f₁ `$ x , proj₂ (F (same _) (x , X))

_`,'_ : ∀ {n Γ} {σ τ : ty n} (A : Γ ⊩ σ) (B : Γ ⊩ τ) → Γ ⊩ σ `× τ
a , A `,' b , B = a `, b , inj₂ (a `, b , (a , A) , (b , B))

`π₁' : ∀ {n Γ} {σ τ : ty n} (P : Γ ⊩ σ `× τ) → Γ ⊩ σ
`π₁' (p , inj₁ P) = `π₁ p , inj₁ (`π₁ P)
`π₁' (p₁ , inj₂ (p₂ , P)) = `π₁ p₁ , proj₂ (proj₁ P)

`π₂' : ∀ {n Γ} {σ τ : ty n} (P : Γ ⊩ σ `× τ) → Γ ⊩ τ
`π₂' (p , inj₁ P) = `π₂ p , inj₁ (`π₂ P)
`π₂' (p₁ , inj₂ (p₂ , P)) = `π₂ p₁ , proj₂ (proj₂ P)

_`∷'_ : ∀ {n Γ} {σ : ty n} (HD : Γ ⊩ σ) (TL : Γ ⊩ `list σ) → Γ ⊩ `list σ
hd , HD `∷' tl , TL = hd `∷ tl , inj₂ (hd `∷ tl , (hd , HD) `∷ (tl , TL))

_`++'_ : ∀ {n Γ} {σ : ty n} (XS : Γ ⊩ `list σ) (YS : Γ ⊩ `list σ) → Γ ⊩ `list σ
xs , inj₁ XS `++' ys , YS = xs `++ ys , inj₁ (XS `++ ys)
xs₁ , inj₂ (xs₂ , `[]) `++' ys , YS = xs₁ `++ ys , YS
xs₁ , inj₂ (xs₂ , HD `∷ TL) `++' ys , YS = xs₁ `++ ys , proj₂ (HD `∷' (TL `++' (ys , YS)))

`map' : ∀ {n Γ} {σ τ : ty n} (F : Γ ⊩ σ `→ τ) (XS : Γ ⊩ `list σ) → Γ ⊩ `list τ
`map' (f , F) (xs , inj₁ XS) = `map f xs , inj₁ (`map f XS)
`map' (f , F) (xs₁ , inj₂ (xs₂ , `[])) = `map f xs₁ , inj₂ (`[] , `[])
`map' (f , F) (xs₁ , inj₂ (xs₂ , HD `∷ TL)) =
  `map f xs₁ , proj₂ ((f , F) `$' HD `∷' `map' (f , F) TL)

`fold' : ∀ {n Γ} {σ τ : ty n} (C : Γ ⊩ σ `→ τ `→ τ) (N : Γ ⊩ τ) (XS : Γ ⊩ `list σ) → Γ ⊩ τ
`fold' (c , C) (n , N) (xs , inj₁ XS) = `fold c n xs , inj₁ (`fold c n XS)
`fold' (c , C) (n , N) (xs₁ , inj₂ (xs₂ , `[])) = `fold c n xs₁ , N
`fold' (c , C) (n , N) (xs₁ , inj₂ (xs₂ , HD `∷ TL)) =
  `fold c n xs₁ , proj₂ ((c , C) `$' HD `$' `fold' (c , C) (n , N) TL)

lookup : ∀ {n Δ Γ} {σ : ty n} (pr : σ ∈ Γ) (ρ : Δ ⊩ε Γ) → Δ ⊩ σ
lookup here!      (_ , r) = r
lookup (there pr) (ρ , _) = lookup pr ρ

eval : ∀ {n Γ Δ} {σ : ty n} (t : Γ ⊢ σ) (ρ : Δ ⊩ε Γ) → Δ ⊩ σ
eval (`v pr) ρ = lookup pr ρ
eval {Γ = Γ} (`λ t) ρ =
  let env = pull Γ ρ in
  subst (`λ t) env , inj₂ (`λ (subst t (⊢ε-weaken Γ (step (same _)) env , `v here!)) ,
  λ inc s → eval t (weaken-⊩ε Γ inc ρ , s))
eval (f `$ x) ρ = eval f ρ `$' eval x ρ
eval `⟨⟩ ρ = `⟨⟩ , inj₂ (`⟨⟩ , tt)
eval {Γ} (a `, b) ρ = eval a ρ `,' eval b ρ
eval (`π₁ t) ρ = `π₁' (eval t ρ)
eval (`π₂ t) ρ = `π₂' (eval t ρ)
eval `[] ρ = `[] , inj₂ (`[] , `[])
eval {Γ} (hd `∷ tl) ρ = eval hd ρ `∷' eval tl ρ
eval (xs `++ ys) ρ = eval xs ρ `++' eval ys ρ
eval (`map f xs) ρ = `map' (eval f ρ) (eval xs ρ)
eval (`fold c n xs) ρ = `fold' (eval c ρ) (eval n ρ) (eval xs ρ)

wh-norm : ∀ {n Γ} {σ : ty n} (t : Γ ⊢ σ) → Γ ⊢whnf σ
wh-norm {Γ = Γ} t = ↑[ _ ] eval t (Γ⊩ε Γ)

open import Data.Empty
open import Relation.Binary.PropositionalEquality

id : ∀ {n Γ} {σ : ty n} → Γ ⊢ σ `→ σ
id = `λ (`v here!)

id² : ∀ {n} → back-whnf {n} {ε} {`1 `→ `1} (wh-norm (id `$ id)) ≡ id
id² = refl

`λid² : ∀ {n} → back-whnf {n} {ε} {`1 `→ `1 `→ `1} (wh-norm (`λ (id `$ id))) ≡ `λ id → ⊥
`λid² ()