module stlcl.definition where

open import Data.Unit
open import Data.Product
open import Data.List
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

cong₃ : ∀ {A B C D : Set} (f : A → B → C → D) {a a' b b' c c'}
        (eqa : a ≡ a') (eqb : b ≡ b') (eqc : c ≡ c') → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

open import tools.contexts

infixr 10 _`→_ _`,_
infixl 10 _`$_
infix 5 _⊢_ _⊢ε_

data ty : Set where
  `1 : ty
  _`×_ _`→_ : (σ τ : ty) → ty
  `list_ : (σ : ty) → ty

{- Well-typed terms in context ;
   Well-typed environments in context -}

data _⊢_ (Γ : Con ty) : ty → Set where
-- usual stlc
  `v : ∀ {σ} (pr : σ ∈ Γ) → Γ ⊢ σ
  `λ : ∀ {σ τ} (t : Γ ∙ σ ⊢ τ) → Γ ⊢ σ `→ τ
  _`$_ : ∀ {σ τ} (t : Γ ⊢ σ `→ τ) (u : Γ ⊢ σ) → Γ ⊢ τ
-- unit and product
  `⟨⟩ : Γ ⊢ `1
  _`,_ : ∀ {σ τ} (a : Γ ⊢ σ) (b : Γ ⊢ τ) → Γ ⊢ σ `× τ
  `π₁ : ∀ {σ τ} (p : Γ ⊢ σ `× τ) → Γ ⊢ σ
  `π₂ : ∀ {σ τ} (p : Γ ⊢ σ `× τ) → Γ ⊢ τ
-- lists
  `[] : ∀ {σ} → Γ ⊢ `list σ
  _`∷_ : ∀ {σ} (hd : Γ ⊢ σ) (tl : Γ ⊢ `list σ) → Γ ⊢ `list σ
  _`++_ : ∀ {σ} (xs ys : Γ ⊢ `list σ) → Γ ⊢ `list σ
  `map : ∀ {σ τ} (f : Γ ⊢ σ `→ τ) (xs : Γ ⊢ `list σ) → Γ ⊢ `list τ
  `fold : ∀ {σ τ} (c : Γ ⊢ σ `→ τ `→ τ) (n : Γ ⊢ τ) (xs : Γ ⊢ `list σ) → Γ ⊢ τ

_⊢ε_ : ∀ (Δ Γ : Con ty) → Set
Δ ⊢ε ε = ⊤
Δ ⊢ε Γ ∙ σ = Δ ⊢ε Γ × Δ ⊢ σ

{- weakenings -}

⊢-weaken : ∀ {Γ Δ σ} (inc : Γ ⊆ Δ) (t : Γ ⊢ σ) → Δ ⊢ σ
⊢-weaken inc (`v pr) = `v (inc-in inc pr)
⊢-weaken inc (`λ t) = `λ (⊢-weaken (pop! inc) t)
⊢-weaken inc (f `$ x) = ⊢-weaken inc f `$ ⊢-weaken inc x
⊢-weaken inc `⟨⟩ = `⟨⟩
⊢-weaken inc (a `, b) = ⊢-weaken inc a `, ⊢-weaken inc b
⊢-weaken inc (`π₁ t) = `π₁ (⊢-weaken inc t)
⊢-weaken inc (`π₂ t) = `π₂ (⊢-weaken inc t)
⊢-weaken inc `[] = `[]
⊢-weaken inc (hd `∷ tl) = ⊢-weaken inc hd `∷ ⊢-weaken inc tl
⊢-weaken inc (xs `++ ys) = ⊢-weaken inc xs `++ ⊢-weaken inc ys
⊢-weaken inc (`map f xs) = `map (⊢-weaken inc f) (⊢-weaken inc xs)
⊢-weaken inc (`fold c n xs) = `fold (⊢-weaken inc c) (⊢-weaken inc n) (⊢-weaken inc xs)

⊢ε-weaken : ∀ Γ {Δ Ε} (inc : Δ ⊆ Ε) (ρ : Δ ⊢ε Γ) → Ε ⊢ε Γ
⊢ε-weaken ε inc ρ = ρ
⊢ε-weaken (Γ ∙ σ) inc (ρ , r) = ⊢ε-weaken Γ inc ρ , ⊢-weaken inc r

{- deleting superfluous elements / "anti-weakening" -}

purge : ∀ {Γ Δ Ε} (pr : Γ ⊆ Δ) (ρ : Ε ⊢ε Δ) → Ε ⊢ε Γ
purge base ρ = ρ
purge (step inc) (ρ , _) = purge inc ρ
purge (pop! inc) (ρ , r) = purge inc ρ , r

⊢ε-weaken-purge : ∀ {Γ Δ Ε Φ} (pr₁ : Γ ⊆ Δ) (pr₂ : Ε ⊆ Φ) (ρ : Ε ⊢ε Δ) →
                  ⊢ε-weaken Γ pr₂ (purge pr₁ ρ) ≡ purge pr₁ (⊢ε-weaken Δ pr₂ ρ)
⊢ε-weaken-purge base pr₂ ρ = refl
⊢ε-weaken-purge (step inc) pr₂ (ρ , _) = ⊢ε-weaken-purge inc pr₂ ρ
⊢ε-weaken-purge (pop! inc) pr₂ (ρ , r) = cong (λ ρ → ρ , ⊢-weaken pr₂ r) (⊢ε-weaken-purge inc pr₂ ρ)

{- substitutions induced by environments -}

get : ∀ {Δ Γ σ} (pr : σ ∈ Γ) (ρ : Δ ⊢ε Γ) → Δ ⊢ σ
get here! (_ , r) = r
get (there pr) (ρ , _) = get pr ρ

subst : ∀ {Γ Δ σ} (t : Γ ⊢ σ) (ρ : Δ ⊢ε Γ) → Δ ⊢ σ
subst (`v pr) ρ = get pr ρ
subst {Γ} (`λ t) ρ = `λ (subst t (⊢ε-weaken Γ (step (same _)) ρ , `v here!))
subst (f `$ x) ρ = subst f ρ `$ subst x ρ
subst `⟨⟩ ρ = `⟨⟩
subst (a `, b) ρ = subst a ρ `, subst b ρ
subst (`π₁ t) ρ = `π₁ (subst t ρ)
subst (`π₂ t) ρ = `π₂ (subst t ρ)
subst `[] ρ = `[]
subst (hd `∷ tl) ρ = subst hd ρ `∷ subst tl ρ
subst (xs `++ ys) ρ = subst xs ρ `++ subst ys ρ
subst (`map f xs) ρ = `map (subst f ρ) (subst xs ρ)
subst (`fold c n xs) ρ = `fold (subst c ρ) (subst n ρ) (subst xs ρ)

⊢ε² : ∀ {Δ Ε} Γ (ρ₁ : Δ ⊢ε Γ) (ρ₂ : Ε ⊢ε Δ) → Ε ⊢ε Γ
⊢ε² ε ρ₁ ρ₂ = tt
⊢ε² (Γ ∙ γ) (ρ₁ , r₁) ρ₂ = ⊢ε² Γ ρ₁ ρ₂ , subst r₁ ρ₂

{- identity weakening -}

⊢-weaken-refl : ∀ {Γ σ} (t : Γ ⊢ σ) → ⊢-weaken (same _) t ≡ t
⊢-weaken-refl (`v pr) = cong `v (inc-in-same pr)
⊢-weaken-refl (`λ t) = cong `λ (⊢-weaken-refl t)
⊢-weaken-refl (f `$ x) = cong₂ _`$_ (⊢-weaken-refl f) (⊢-weaken-refl x)
⊢-weaken-refl `⟨⟩ = refl
⊢-weaken-refl (a `, b) = cong₂ _`,_ (⊢-weaken-refl a) (⊢-weaken-refl b)
⊢-weaken-refl (`π₁ t) =  cong `π₁ (⊢-weaken-refl t)
⊢-weaken-refl (`π₂ t) =  cong `π₂ (⊢-weaken-refl t)
⊢-weaken-refl `[] = refl
⊢-weaken-refl (hd `∷ tl) = cong₂ _`∷_ (⊢-weaken-refl hd) (⊢-weaken-refl tl)
⊢-weaken-refl (xs `++ ys) = cong₂ _`++_ (⊢-weaken-refl xs) (⊢-weaken-refl ys)
⊢-weaken-refl (`map f xs) = cong₂ `map (⊢-weaken-refl f) (⊢-weaken-refl xs)
⊢-weaken-refl (`fold c n xs) = cong₃ `fold (⊢-weaken-refl c) (⊢-weaken-refl n) (⊢-weaken-refl xs)

⊢ε-weaken-refl : ∀ {Δ} Γ (ρ : Δ ⊢ε Γ) → ⊢ε-weaken Γ (same _) ρ ≡ ρ
⊢ε-weaken-refl ε ρ = refl
⊢ε-weaken-refl (Γ ∙ σ) (ρ , r) = cong₂ _,_ (⊢ε-weaken-refl Γ ρ) (⊢-weaken-refl r)

{- weakenings fusion -}

⊢-weaken² : ∀ {Γ Δ Ε σ} (inc : Γ ⊆ Δ) (inc' : Δ ⊆ Ε) (t : Γ ⊢ σ) →
            ⊢-weaken inc' (⊢-weaken inc t) ≡ ⊢-weaken (⊆-trans inc inc') t
⊢-weaken² inc inc' (`v pr) = cong `v (inc-in² inc inc' pr)
⊢-weaken² inc inc' (`λ t) = cong `λ (⊢-weaken² (pop! inc) (pop! inc') t)
⊢-weaken² inc inc' (f `$ x) = cong₂ _`$_ (⊢-weaken² inc inc' f) (⊢-weaken² inc inc' x)
⊢-weaken² inc inc' `⟨⟩ = refl
⊢-weaken² inc inc' (a `, b) = cong₂ _`,_ (⊢-weaken² inc inc' a) (⊢-weaken² inc inc' b)
⊢-weaken² inc inc' (`π₁ t) = cong `π₁ (⊢-weaken² inc inc' t)
⊢-weaken² inc inc' (`π₂ t) = cong `π₂ (⊢-weaken² inc inc' t)
⊢-weaken² inc inc' `[] = refl
⊢-weaken² inc inc' (hd `∷ tl) = cong₂ _`∷_ (⊢-weaken² inc inc' hd) (⊢-weaken² inc inc' tl)
⊢-weaken² inc inc' (xs `++ ys) = cong₂ _`++_ (⊢-weaken² inc inc' xs) (⊢-weaken² inc inc' ys)
⊢-weaken² inc inc' (`map f xs) = cong₂ `map (⊢-weaken² inc inc' f) (⊢-weaken² inc inc' xs)
⊢-weaken² inc inc' (`fold c n xs) =
  cong₃ `fold (⊢-weaken² inc inc' c) (⊢-weaken² inc inc' n) (⊢-weaken² inc inc' xs)

⊢ε-weaken² : ∀ Γ {Δ Ε Φ} (inc : Δ ⊆ Ε) (inc' : Ε ⊆ Φ) (ρ : Δ ⊢ε Γ) →
             ⊢ε-weaken Γ inc' (⊢ε-weaken Γ inc ρ) ≡ ⊢ε-weaken Γ (⊆-trans inc inc') ρ
⊢ε-weaken² ε inc inc' ρ = refl
⊢ε-weaken² (Γ ∙ σ) inc inc' (ρ , r) = cong₂ _,_ (⊢ε-weaken² Γ inc inc' ρ) (⊢-weaken² inc inc' r)

{- canonical environment -}

⊢ε-refl : (Γ : Con ty) → Γ ⊢ε Γ
⊢ε-refl ε = tt
⊢ε-refl (Γ ∙ σ) = ⊢ε-weaken Γ (step (same _)) (⊢ε-refl Γ) , `v here!

purge-⊢ε-refl : ∀ {Γ Δ} (pr : Γ ⊆ Δ) → purge pr (⊢ε-refl Δ) ≡ ⊢ε-weaken Γ pr (⊢ε-refl Γ)
purge-⊢ε-refl base = refl
purge-⊢ε-refl (step {Γ} {Δ} {σ} pr) =
  trans (sym (⊢ε-weaken-purge pr _ (⊢ε-refl Δ))) (trans (cong (⊢ε-weaken Γ _) (purge-⊢ε-refl pr))
  (trans (⊢ε-weaken² Γ pr _ (⊢ε-refl Γ)) (cong (λ pr → ⊢ε-weaken Γ pr (⊢ε-refl Γ))
  (trans (sym (⊆-step-same pr)) (cong step (⊆-same-l pr))))))
purge-⊢ε-refl (pop! {Γ} {Δ} {σ} pr) =
  cong (λ ρ → ρ , `v here!) (trans (trans (sym (⊢ε-weaken-purge pr _ (⊢ε-refl Δ)))
  (cong (⊢ε-weaken Γ _) (purge-⊢ε-refl pr))) (trans (⊢ε-weaken² Γ pr _ (⊢ε-refl Γ))
  (trans (cong (λ pr → ⊢ε-weaken Γ pr (⊢ε-refl Γ)) (sym (⊆-step-same pr)))
  (sym (⊢ε-weaken² Γ _ (pop! pr) (⊢ε-refl Γ))))))

{- identity substitution -}

get-refl-weaken : ∀ {Γ Δ σ} (pr : σ ∈ Γ) (inc : Γ ⊆ Δ) →
                  get pr (⊢ε-weaken Γ inc (⊢ε-refl Γ)) ≡ `v (inc-in inc pr)
get-refl-weaken {ε} () inc
get-refl-weaken here! inc = refl
get-refl-weaken {Γ ∙ σ} (there pr) inc =
  trans (cong (get pr) (⊢ε-weaken² Γ (step (same _)) inc (⊢ε-refl Γ)))
 (trans (get-refl-weaken {Γ} pr _) (cong `v (inc-in-step inc pr)))

get-refl : ∀ {Γ σ} (pr : σ ∈ Γ) → get pr (⊢ε-refl Γ) ≡ `v pr
get-refl {Γ} pr =
  trans (cong (get pr) (sym (⊢ε-weaken-refl Γ (⊢ε-refl Γ))))
 (trans (get-refl-weaken pr (same _)) (cong `v (inc-in-same pr)))

subst-refl : ∀ {Γ σ} (t : Γ ⊢ σ) → subst t (⊢ε-refl Γ) ≡ t
subst-refl (`v pr) = get-refl pr
subst-refl (`λ t) = cong `λ (subst-refl t)
subst-refl (f `$ x) = cong₂ _`$_ (subst-refl f) (subst-refl x)
subst-refl `⟨⟩ = refl
subst-refl (a `, b) = cong₂ _`,_ (subst-refl a) (subst-refl b)
subst-refl (`π₁ t) = cong `π₁ (subst-refl t)
subst-refl (`π₂ t) = cong `π₂ (subst-refl t)
subst-refl `[] = refl
subst-refl (hd `∷ tl) = cong₂ _`∷_ (subst-refl hd) (subst-refl tl)
subst-refl (xs `++ ys) = cong₂ _`++_ (subst-refl xs) (subst-refl ys)
subst-refl (`map f xs) = cong₂ `map (subst-refl f) (subst-refl xs)
subst-refl (`fold c n xs) = cong₃ `fold (subst-refl c) (subst-refl n) (subst-refl xs)

{- identity purge ; composition -}

purge-refl : ∀ Γ {Δ} (ρ : Δ ⊢ε Γ) → purge (same Γ) ρ ≡ ρ
purge-refl ε ρ = refl
purge-refl (Γ ∙ σ) (ρ , r) = cong (λ ρ → ρ , r) (purge-refl Γ ρ)

⊢ε²-refl : ∀ {Δ} Γ (ρ : Δ ⊢ε Γ) → ⊢ε² Γ ρ (⊢ε-refl Δ) ≡ ρ
⊢ε²-refl ε ρ = refl
⊢ε²-refl (Γ ∙ σ) (ρ , r) = cong₂ _,_ (⊢ε²-refl Γ ρ) (subst-refl r)

{- subst weaken fusion -}

weaken-get : ∀ {Γ Δ Ε σ} (pr : σ ∈ Γ) (inc : Δ ⊆ Ε) (ρ : Δ ⊢ε Γ) →
             ⊢-weaken inc (get pr ρ) ≡ get pr (⊢ε-weaken Γ inc ρ)
weaken-get here! inc ρ = refl
weaken-get (there {- if we want to -} pr) inc (ρ , _) = weaken-get pr inc ρ

weaken-subst : ∀ {Γ Δ Ε σ} (inc : Δ ⊆ Ε) (t : Γ ⊢ σ) (ρ : Δ ⊢ε Γ) →
               ⊢-weaken inc (subst t ρ) ≡ subst t (⊢ε-weaken Γ inc ρ)
weaken-subst inc (`v pr) ρ = weaken-get pr inc ρ
weaken-subst {Γ} inc (`λ t) ρ =
  cong `λ (trans (weaken-subst (pop! inc) t _) (cong (λ ρ → subst t (ρ , `v here!))
  (trans (⊢ε-weaken² Γ _ _ ρ) (trans (cong (λ inc → ⊢ε-weaken Γ inc ρ) (⊆-step-same inc))
  (sym (⊢ε-weaken² Γ _ _ ρ))))))
weaken-subst inc (f `$ x) ρ = cong₂ _`$_ (weaken-subst inc f ρ) (weaken-subst inc x ρ)
weaken-subst inc `⟨⟩ ρ = refl
weaken-subst inc (a `, b) ρ = cong₂ _`,_ (weaken-subst inc a ρ) (weaken-subst inc b ρ)
weaken-subst inc (`π₁ t) ρ = cong `π₁ (weaken-subst inc t ρ)
weaken-subst inc (`π₂ t) ρ = cong `π₂ (weaken-subst inc t ρ)
weaken-subst inc `[] ρ = refl
weaken-subst inc (hd `∷ tl) ρ = cong₂ _`∷_ (weaken-subst inc hd ρ) (weaken-subst inc tl ρ)
weaken-subst inc (xs `++ ys) ρ = cong₂ _`++_ (weaken-subst inc xs ρ) (weaken-subst inc ys ρ)
weaken-subst inc (`map f xs) ρ = cong₂ `map (weaken-subst inc f ρ) (weaken-subst inc xs ρ)
weaken-subst inc (`fold c n xs) ρ =
  cong₃ `fold (weaken-subst inc c ρ) (weaken-subst inc n ρ) (weaken-subst inc xs ρ)

get-inc : ∀ {Γ Δ Ε σ} (inc : Γ ⊆ Δ) (pr : σ ∈ Γ) (ρ : Ε ⊢ε Δ) →
          get (inc-in inc pr) ρ ≡ get pr (purge inc ρ)
get-inc base () _
get-inc (step inc) here! (ρ , _) = get-inc inc here! ρ
get-inc (pop! inc) here! ρ = refl
get-inc (step inc) (there pr) (ρ , _) = get-inc inc (there pr) ρ
get-inc (pop! inc) (there pr) (ρ , _) = get-inc inc pr ρ

subst-weaken : ∀ {Γ Δ Ε σ} (inc : Γ ⊆ Δ) (t : Γ ⊢ σ) (ρ : Ε ⊢ε Δ) →
               subst (⊢-weaken inc t) ρ ≡ subst t (purge inc ρ)
subst-weaken inc (`v pr) ρ = get-inc inc pr ρ
subst-weaken inc (`λ t) ρ =
  cong `λ (trans (subst-weaken (pop! inc) t _) (cong (λ ρ → subst t (ρ , `v here!))
  (sym (⊢ε-weaken-purge inc (step (⊆-refl _)) ρ))))
subst-weaken inc (f `$ x) ρ = cong₂ _`$_ (subst-weaken inc f ρ) (subst-weaken inc x ρ)
subst-weaken inc `⟨⟩ ρ = refl
subst-weaken inc (a `, b) ρ = cong₂ _`,_ (subst-weaken inc a ρ) (subst-weaken inc b ρ)
subst-weaken inc (`π₁ t) ρ = cong `π₁ (subst-weaken inc t ρ)
subst-weaken inc (`π₂ t) ρ = cong `π₂ (subst-weaken inc t ρ)
subst-weaken inc `[] ρ = refl
subst-weaken inc (hd `∷ tl) ρ = cong₂ _`∷_ (subst-weaken inc hd ρ) (subst-weaken inc tl ρ)
subst-weaken inc (xs `++ ys) ρ = cong₂ _`++_ (subst-weaken inc xs ρ) (subst-weaken inc ys ρ)
subst-weaken inc (`map f xs) ρ = cong₂ `map (subst-weaken inc f ρ) (subst-weaken inc xs ρ)
subst-weaken inc (`fold c n xs) ρ =
  cong₃ `fold (subst-weaken inc c ρ) (subst-weaken inc n ρ) (subst-weaken inc xs ρ)

{- environment composition simplification -}

⊢ε²-weaken : ∀ {Δ Ε Φ} Γ (pr : Ε ⊆ Φ) (ρ₁ : Δ ⊢ε Γ) (ρ₂ : Ε ⊢ε Δ) →
             ⊢ε-weaken Γ pr (⊢ε² Γ ρ₁ ρ₂) ≡ ⊢ε² Γ ρ₁ (⊢ε-weaken Δ pr ρ₂)
⊢ε²-weaken ε pr ρ₁ ρ₂ = refl
⊢ε²-weaken (Γ ∙ σ) pr (ρ₁ , r₁) ρ₂ = cong₂ _,_ (⊢ε²-weaken Γ pr ρ₁ ρ₂) (weaken-subst pr r₁ ρ₂)

⊢ε²-step : ∀ {Δ Ε σ} Γ (ρ₁ : Δ ⊢ε Γ) (ρ₂ : Ε ⊢ε Δ) (s : Ε ⊢ σ) →
           ⊢ε² Γ (⊢ε-weaken Γ (step (same Δ)) ρ₁) (ρ₂ , s) ≡ ⊢ε² Γ ρ₁ ρ₂
⊢ε²-step ε ρ₁ ρ₂ s = refl
⊢ε²-step {Δ} (Γ ∙ σ) (ρ₁ , r₁) ρ₂ s =
  cong₂ _,_ (⊢ε²-step Γ ρ₁ ρ₂ s) (trans (subst-weaken (step (same _)) r₁ (ρ₂ , s))
  (cong (subst r₁) (purge-refl Δ ρ₂)))

{- substitutions fusion -}

get-⊢ε² : ∀ {Γ Δ Ε σ} (pr : σ ∈ Γ) (ρ₁ : Δ ⊢ε Γ) (ρ₂ : Ε ⊢ε Δ) →
           subst (get pr ρ₁) ρ₂ ≡ get pr (⊢ε² Γ ρ₁ ρ₂)
get-⊢ε² here! ρ₁ ρ₂ = refl
get-⊢ε² (there pr) (ρ₁ , _) ρ₂ = get-⊢ε² pr ρ₁ ρ₂

subst² : ∀ {Γ Δ Ε σ} (t : Γ ⊢ σ) (ρ₁ : Δ ⊢ε Γ) (ρ₂ : Ε ⊢ε Δ) →
             subst (subst t ρ₁) ρ₂ ≡ subst t (⊢ε² Γ ρ₁ ρ₂)
subst² (`v pr) ρ₁ ρ₂ = get-⊢ε² pr ρ₁ ρ₂
subst² {Γ} {Δ} {Ε} (`λ t) ρ₁ ρ₂ =
  cong `λ (trans (subst² t _ _) (cong (λ ρ → subst t (ρ , `v here!))
  (trans (⊢ε²-step Γ ρ₁ _ (`v here!)) (sym (⊢ε²-weaken Γ _ ρ₁ ρ₂)))))
subst² (f `$ x) ρ₁ ρ₂ = cong₂ _`$_ (subst² f ρ₁ ρ₂) (subst² x ρ₁ ρ₂)
subst² `⟨⟩ ρ₁ ρ₂ = refl
subst² (a `, b) ρ₁ ρ₂ = cong₂ _`,_ (subst² a ρ₁ ρ₂) (subst² b ρ₁ ρ₂)
subst² (`π₁ t) ρ₁ ρ₂ = cong `π₁ (subst² t ρ₁ ρ₂)
subst² (`π₂ t) ρ₁ ρ₂ = cong `π₂ (subst² t ρ₁ ρ₂)
subst² `[] ρ₁ ρ₂ = refl
subst² (hd `∷ tl) ρ₁ ρ₂ = cong₂ _`∷_ (subst² hd ρ₁ ρ₂) (subst² tl ρ₁ ρ₂)
subst² (xs `++ ys) ρ₁ ρ₂ = cong₂ _`++_ (subst² xs ρ₁ ρ₂) (subst² ys ρ₁ ρ₂)
subst² (`map f xs) ρ₁ ρ₂ = cong₂ `map (subst² f ρ₁ ρ₂) (subst² xs ρ₁ ρ₂)
subst² (`fold c n xs) ρ₁ ρ₂ = cong₃ `fold (subst² c ρ₁ ρ₂) (subst² n ρ₁ ρ₂) (subst² xs ρ₁ ρ₂)

subst-pop : ∀ {Δ Γ σ τ} (t : Γ ⊢ σ) (s : Δ ⊢ τ) (inc : Γ ⊆ Δ) →
  ⊢-weaken inc t ≡ subst (⊢-weaken (pop! inc) (⊢-weaken (step (same _)) t)) (⊢ε-refl Δ , s)
subst-pop {Δ} t s inc =
  trans (trans (trans (sym (subst-refl (⊢-weaken inc t))) (trans (subst-weaken inc t (⊢ε-refl Δ))
  (cong (λ pr → subst t (purge pr (⊢ε-refl Δ))) (sym (⊆-same-l inc)))))
  (sym (subst-weaken (⊆-trans (step (same _)) (pop! inc)) t (⊢ε-refl Δ , s))))
  (cong (λ t → subst t (⊢ε-refl Δ , s)) (sym (⊢-weaken² (step (same _)) (pop! inc) t)))