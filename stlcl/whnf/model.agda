module stlcl.whnf.model where

open import Data.Unit
open import Data.Sum
open import Data.Product

open import tools.contexts
open import stlcl.definition
open import stlcl.normalforms

infix 10 _⊩_

data _⊩list_by_ (Γ : Con ty) σ (Σ : Con ty → Set) : Set where
  `[]   : Γ ⊩list σ by Σ
  _`∷_  : ∀ (HD : Σ Γ) (TL : Γ ⊢ `list σ × (Γ ⊢whne `list σ ⊎ Γ ⊢whnf `list σ × Γ ⊩list σ by Σ)) →
          Γ ⊩list σ by Σ

mutual

  _⊩'_ : Con ty → ty → Set
  Γ ⊩' `1 = ⊤
  Γ ⊩' σ `× τ = Γ ⊩ σ × Γ ⊩ τ
  Γ ⊩' σ `→ τ = ∀ {Δ} (inc : Γ ⊆ Δ) → Δ ⊩ σ → Δ ⊩ τ
  Γ ⊩' `list σ = Γ ⊩list σ by λ Δ → Δ ⊩ σ

  _⊩_ : Con ty → ty → Set
  Γ ⊩ σ = Γ ⊢ σ × (Γ ⊢whne σ ⊎ Γ ⊢whnf σ × Γ ⊩' σ)

weaken-⊩list : ∀ {Γ Δ σ Σ} (inc : Γ ⊆ Δ) (weaken-Σ : Σ Γ → Σ Δ) →
  Γ ⊩list σ by Σ → Δ ⊩list σ by Σ
weaken-⊩list inc weaken-Σ `[] = `[]
weaken-⊩list inc weaken-Σ (HD `∷ (tl , inj₁ TL)) =
  weaken-Σ HD `∷
  (⊢-weaken inc tl , inj₁ (weaken-whne inc TL))
weaken-⊩list inc weaken-Σ (HD `∷ (tl₁ , inj₂ (tl₂ , TL))) =
  weaken-Σ HD `∷
  (⊢-weaken inc tl₁ , inj₂ (weaken-whnf inc tl₂ , weaken-⊩list inc weaken-Σ TL))

mutual

  weaken-⊩' : ∀ σ {Γ Δ} (inc : Γ ⊆ Δ) (T : Γ ⊩' σ) → Δ ⊩' σ
  weaken-⊩' `1 inc T = T
  weaken-⊩' (σ `× τ) inc (A , B) = weaken-⊩ inc A , weaken-⊩ inc B
  weaken-⊩' (σ `→ τ) inc F = λ inc' S → F (⊆-trans inc inc') S
  weaken-⊩' (`list σ) inc XS = weaken-⊩list inc (weaken-⊩ {σ} inc) XS

  weaken-⊩ : ∀ {σ Γ Δ} (inc : Γ ⊆ Δ) (T : Γ ⊩ σ) → Δ ⊩ σ
  weaken-⊩ inc (t , inj₁ T) =
    ⊢-weaken inc t , inj₁ (weaken-whne inc T)
  weaken-⊩ {σ} inc (t₁ , inj₂ (t₂ , T)) =
    ⊢-weaken inc t₁ , inj₂ (weaken-whnf inc t₂ , weaken-⊩' σ inc T)

↑[_]_ : ∀ {Γ} σ (T : Γ ⊩ σ) → Γ ⊢whnf σ
↑[ σ ] (t , inj₁ T) = `↑ T
↑[ σ ] (t , inj₂ T) = proj₁ T

↓[_]_ : ∀ {Γ} σ (t : Γ ⊢whne σ) → Γ ⊩ σ
↓[ σ ] t = back-whne t , inj₁ t

_⊩ε_ : (Δ Γ : Con ty) → Set
Δ ⊩ε ε = ⊤
Δ ⊩ε Γ ∙ σ = Δ ⊩ε Γ × Δ ⊩ σ

weaken-⊩ε : ∀ Γ {Δ Ε} (inc : Δ ⊆ Ε) (ρ : Δ ⊩ε Γ) → Ε ⊩ε Γ
weaken-⊩ε ε inc ρ = ρ
weaken-⊩ε (Γ ∙ σ) inc (ρ , r) = weaken-⊩ε Γ inc ρ , weaken-⊩ inc r

Γ⊩ε_ : (Γ : Con ty) → Γ ⊩ε Γ
Γ⊩ε ε = tt
Γ⊩ε Γ ∙ σ = weaken-⊩ε Γ (step (same _)) (Γ⊩ε Γ) , ↓[ σ ] `v here!

pull : ∀ {Δ} Γ → Δ ⊩ε Γ → Δ ⊢ε Γ
pull ε ρ = ρ
pull (Γ ∙ σ) (ρ , (r , _)) = pull Γ ρ , r

infixl 1 _`$'_
infixr 1 _`++'_

_`$'_ : ∀ {Γ σ τ} (F : Γ ⊩ σ `→ τ) (X : Γ ⊩ σ) → Γ ⊩ τ
f , inj₁ F `$' x , X = f `$ x , inj₁ (F `$ x)
f₁ , inj₂ (f₂ , F) `$' X = F (same _) X

`π₁' : ∀ {Γ σ τ} (P : Γ ⊩ σ `× τ) → Γ ⊩ σ
`π₁' (p , inj₁ P) = `π₁ p , inj₁ (`π₁ P)
`π₁' (p₁ , inj₂ (p₂ , P)) = proj₁ P

`π₂' : ∀ {Γ σ τ} (P : Γ ⊩ σ `× τ) → Γ ⊩ τ
`π₂' (p , inj₁ P) = `π₂ p , inj₁ (`π₂ P)
`π₂' (p₁ , inj₂ (p₂ , P)) = proj₂ P

_`++'_ : ∀ {Γ σ} (XS : Γ ⊩ `list σ) (YS : Γ ⊩ `list σ) → Γ ⊩ `list σ
xs , inj₁ XS `++' ys , YS = xs `++ ys , inj₁ (XS `++ ys)
xs₁ , inj₂ (xs₂ , `[]) `++' ys , YS = xs₁ `++ ys , YS
xs₁ , inj₂ (xs₂ , (hd , HD) `∷ TL') `++' YS' =
  let tl , TL = TL'
      ys , YS = YS' in
  xs₁ `++ ys , inj₂ (hd `∷ (tl `++ ys) , (hd , HD) `∷ (TL' `++' YS'))

`map' : ∀ {Γ σ τ} (F : Γ ⊩ σ `→ τ) (XS : Γ ⊩ `list σ) → Γ ⊩ `list τ
`map' (f , F) (xs , inj₁ XS) = `map f xs , inj₁ (`map f XS)
`map' (f , F) (xs₁ , inj₂ (xs₂ , `[])) = `map f xs₁ , inj₂ (`[] , `[])
`map' F' (xs₁ , inj₂ (xs₂ , HD' `∷ TL')) =
  let f  , F  = F'
      hd , HD = HD'
      tl , TL = TL' in
  `map f xs₁ , inj₂ ((f `$ hd) `∷ `map f tl , (F' `$' HD') `∷ `map' F' TL')

`fold' : ∀ {Γ σ τ} (C : Γ ⊩ σ `→ τ `→ τ) (N : Γ ⊩ τ) (XS : Γ ⊩ `list σ) → Γ ⊩ τ
`fold' (c , C) (n , N) (xs , inj₁ XS) = `fold c n xs , inj₁ (`fold c n XS)
`fold' (c , C) (n , N) (xs₁ , inj₂ (xs₂ , `[])) = `fold c n xs₁ , N
`fold' C' N' (xs₁ , inj₂ (xs₂ , HD' `∷ TL')) =
  let c  , C  = C'
      n  , N  = N'
      hd , HD = HD'
      tl , TL = TL' in
  `fold c n xs₁ , proj₂ (C' `$' HD' `$' `fold' C' N' TL')

lookup : ∀ {Δ Γ σ} (pr : σ ∈ Γ) (ρ : Δ ⊩ε Γ) → Δ ⊩ σ
lookup here! (_ , r) = r
lookup (there pr) (ρ , _) = lookup pr ρ

eval : ∀ {Γ Δ σ} (t : Γ ⊢ σ) (ρ : Δ ⊩ε Γ) → Δ ⊩ σ
eval (`v pr) ρ = lookup pr ρ
eval {Γ} (`λ t) ρ =
  let env = pull Γ ρ in
  subst (`λ t) env , inj₂ (`λ (subst t (⊢ε-weaken Γ (step (same _)) env , `v here!)) ,
  λ inc s → eval t (weaken-⊩ε Γ inc ρ , s))
eval (f `$ x) ρ = eval f ρ `$' eval x ρ
eval `⟨⟩ ρ = `⟨⟩ , inj₂ (`⟨⟩ , tt)
eval {Γ} (a `, b) ρ =
  let env = pull Γ ρ
      a'  = subst a env
      b'  = subst b env in
  a' `, b' , inj₂ (a' `, b' , eval a ρ , eval b ρ)
eval (`π₁ t) ρ = `π₁' (eval t ρ)
eval (`π₂ t) ρ = `π₂' (eval t ρ)
eval `[] ρ = `[] , inj₂ (`[] , `[])
eval {Γ} (hd `∷ tl) ρ =
  let env = pull Γ ρ
      hd' = subst hd env
      tl' = subst tl env in
  hd' `∷ tl' , inj₂ (hd' `∷ tl' , eval hd ρ `∷ eval tl ρ)
eval (xs `++ ys) ρ = eval xs ρ `++' eval ys ρ
eval (`map f xs) ρ = `map' (eval f ρ) (eval xs ρ)
eval (`fold c n xs) ρ = `fold' (eval c ρ) (eval n ρ) (eval xs ρ)

wh-norm : ∀ {Γ σ} (t : Γ ⊢ σ) → Γ ⊢whnf σ
wh-norm {Γ} t = ↑[ _ ] eval t (Γ⊩ε Γ)

-- examples

open import Data.Empty
open import Relation.Binary.PropositionalEquality

id : ∀ {Γ σ} → Γ ⊢ σ `→ σ
id = `λ (`v here!)

id² : back-whnf {ε} {`1 `→ `1} (wh-norm (id `$ id)) ≡ id
id² = refl

`λid² : back-whnf {ε} {`1 `→ `1 `→ `1} (wh-norm (`λ (id `$ id))) ≡ `λ id → ⊥
`λid² ()