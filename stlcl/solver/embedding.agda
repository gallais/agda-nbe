module stlcl.solver.embedding where

open import tools.contexts
open import tools.closures
open import stlcl.definition hiding (purge ; purge-refl)
open import stlcl.reductions
open import stlcl.eqdecide

open import Data.Empty
open import Data.Unit
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.List
open import Data.Vec as Vec using (Vec)
open import Function

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality renaming (subst to coerce)

infix 5 ⟦_⟧_ ⌈_!_⌉ε

{- Interpreation of types and contexts in Agda -}

⟦_⟧_ : ∀ {n} (σ : ty n) (ρ : Vec Set n) → Set
⟦ `b x ⟧ ρ = Vec.lookup x ρ
⟦ `1 ⟧ ρ = ⊤
⟦ σ `× τ ⟧ ρ = ⟦ σ ⟧ ρ × ⟦ τ ⟧ ρ
⟦ σ `→ τ ⟧ ρ = ⟦ σ ⟧ ρ → ⟦ τ ⟧ ρ
⟦ `list σ ⟧ ρ = List (⟦ σ ⟧ ρ)

⟦_⟧ε_ : ∀ {n} (Γ : Con (ty n)) (ρ : Vec Set n) → Set
⟦ ε ⟧ε ρ = ⊤
⟦ Γ ∙ σ ⟧ε ρ = ⟦ Γ ⟧ε ρ × ⟦ σ ⟧ ρ

lookup : ∀ {n Γ} {σ : ty n} (pr : σ ∈ Γ) {ρ} (R : ⟦ Γ ⟧ε ρ) → ⟦ σ ⟧ ρ
lookup here! (_ , r) = r
lookup (there pr) (R , _) = lookup pr R

purge : ∀ {n} {Γ Δ : Con (ty n)} {ρ} (pr : Γ ⊆ Δ) (R : ⟦ Δ ⟧ε ρ) → ⟦ Γ ⟧ε ρ
purge base tt = tt
purge (step pr) (R , r) = purge pr R
purge (pop! pr) (R , r) = purge pr R , r

purge-refl : ∀ {n} (Γ : Con (ty n)) {ρ} (R : ⟦ Γ ⟧ε ρ) → purge (same Γ) R ≡ R
purge-refl ε       R       = refl
purge-refl (Γ ∙ σ) (R , r) rewrite purge-refl Γ R = refl

{- Interpretation of well-typed terms in Agda -}

⌈_⌉ : ∀ {n Γ} {σ : ty n} (t : Γ ⊢ σ) {ρ} → ⟦ Γ ⟧ε ρ → ⟦ σ ⟧ ρ
⌈ `v pr        ⌉ R = lookup pr R
⌈ `λ t         ⌉ R = λ S → ⌈ t ⌉ (R , S)
⌈ f `$ x       ⌉ R = ⌈ f ⌉ R (⌈ x ⌉ R)
⌈ `⟨⟩          ⌉ R = tt
⌈ a `, b       ⌉ R = ⌈ a ⌉ R , ⌈ b ⌉ R
⌈ `π₁ t        ⌉ R = proj₁ (⌈ t ⌉ R)
⌈ `π₂ t        ⌉ R = proj₂ (⌈ t ⌉ R)
⌈ `[]          ⌉ R = []
⌈ hd `∷ tl     ⌉ R = ⌈ hd ⌉ R ∷ ⌈ tl ⌉ R
⌈ xs `++ ys    ⌉ R = ⌈ xs ⌉ R Data.List.++ ⌈ ys ⌉ R
⌈ `map f xs    ⌉ R = map (⌈ f ⌉ R) (⌈ xs ⌉ R)
⌈ `fold c n xs ⌉ R = foldr (⌈ c ⌉ R) (⌈ n ⌉ R) (⌈ xs ⌉ R)

⌈_!_⌉ε : ∀ {n} Γ {Δ : Con (ty n)} (r : Δ ⊢ε Γ) {ρ} → ⟦ Δ ⟧ε ρ → ⟦ Γ ⟧ε ρ
⌈ ε     ! tt      ⌉ε R = tt
⌈ Γ ∙ σ ! rΓ , rσ ⌉ε R = ⌈ Γ ! rΓ ⌉ε R , ⌈ rσ ⌉ R

{- We assume functional extensionality because our equational
   theory allows reduction under lambdas. -}

postulate
  fun-ext : ∀ {A B : Set} {f g : A → B} (eq : ∀ x → f x ≡ g x) → f ≡ g

{- interpreting a weakened term amounts to interpreting this
   term in a purged environment. -}

lookup-purge : ∀ {n Γ Δ ρ} {σ : ty n} (inc : Γ ⊆ Δ) (pr : σ ∈ Γ) (R : ⟦ Δ ⟧ε ρ) →
  lookup (inc-in inc pr) R ≡ lookup pr (purge inc R)
lookup-purge base () R
lookup-purge (step inc) here!      (R , _) = lookup-purge inc here! R
lookup-purge (step inc) (there pr) (R , _) = lookup-purge inc (there pr) R
lookup-purge (pop! inc) here!      (_ , r) = refl
lookup-purge (pop! inc) (there pr) (R , _) = lookup-purge inc pr R

interp-purge : ∀ {n Γ Δ ρ} {σ : ty n} (inc : Γ ⊆ Δ) (t : Γ ⊢ σ) (R : ⟦ Δ ⟧ε ρ) →
  ⌈ ⊢-weaken inc t ⌉ R ≡ ⌈ t ⌉ (purge inc R)
interp-purge inc (`v pr)        R = lookup-purge inc pr R
interp-purge inc (`λ t)         R = fun-ext (λ S → interp-purge (pop! inc) t (R , S))
interp-purge inc (f `$ x)       R = cong₂ _$_ (interp-purge inc f R) (interp-purge inc x R)
interp-purge inc `⟨⟩            R = refl
interp-purge inc (a `, b)       R = cong₂ _,_ (interp-purge inc a R) (interp-purge inc b R)
interp-purge inc (`π₁ p)        R = cong proj₁ (interp-purge inc p R)
interp-purge inc (`π₂ p)        R = cong proj₂ (interp-purge inc p R)
interp-purge inc `[]            R = refl
interp-purge inc (hd `∷ tl)     R = cong₂ _∷_ (interp-purge inc hd R) (interp-purge inc tl R)
interp-purge inc (xs `++ ys)    R = cong₂ _++_ (interp-purge inc xs R) (interp-purge inc ys R)
interp-purge inc (`map f xs)    R = cong₂ map (interp-purge inc f R) (interp-purge inc xs R)
interp-purge inc (`fold c n xs) R =
  cong₃ foldr (interp-purge inc c R) (interp-purge inc n R) (interp-purge inc xs R)

interpε-purge : ∀ {n} Γ {Δ Ε : Con (ty n)} {ρ} (inc : Δ ⊆ Ε) (r : Δ ⊢ε Γ) (R : ⟦ Ε ⟧ε ρ) →
  ⌈ Γ ! ⊢ε-weaken Γ inc r ⌉ε R ≡ ⌈ Γ ! r ⌉ε (purge inc R)
interpε-purge ε       inc tt      R = refl
interpε-purge (Γ ∙ σ) inc (ρ , r) R = cong₂ _,_ (interpε-purge Γ inc ρ R) (interp-purge inc r R)

{--}

interp-⊢ε-refl : ∀ {n} (Γ : Con (ty n)) {ρ} (R : ⟦ Γ ⟧ε ρ) → ⌈ Γ ! ⊢ε-refl Γ ⌉ε R ≡ R
interp-⊢ε-refl ε       R       = refl
interp-⊢ε-refl (Γ ∙ σ) (R , r) =
  let eq = interpε-purge Γ (step {σ = σ} (same Γ)) (⊢ε-refl Γ) (R , r)
  in cong (λ R → R , r) (trans (trans eq
       (cong ⌈ Γ ! ⊢ε-refl Γ ⌉ε (purge-refl Γ R)))
       (interp-⊢ε-refl Γ R))

{- The standardization rules added to our calculus' reduction
   relation are compatible with Agda's propositional equality. -}

comp : ∀ {n Γ} {σ τ υ : ty n} (g : Γ ⊢ τ `→ υ) (f : Γ ⊢ σ `→ τ) ρ (R : ⟦ Γ ⟧ε ρ) →
  ⌈ g `∘ f ⌉ R ≡ ⌈ g ⌉ R ∘ ⌈ f ⌉ R
comp {n} {Γ} {σ} {τ} {υ} g f ρ R = fun-ext (λ S →
  let eqg = interp-purge (step {σ = σ} (same Γ)) g (R , S)
      eqf = interp-purge (step {σ = σ} (same Γ)) f (R , S)
  in cong₂ (λ g f → g $ f S)
     (trans eqg (cong ⌈ g ⌉ (purge-refl Γ R)))
     (trans eqf (cong ⌈ f ⌉ (purge-refl Γ R))))

ηmap₁ : ∀ {A : Set} (xs : List A) → xs ≡ map (λ x → x) xs
ηmap₁ [] = refl
ηmap₁ (x ∷ xs) rewrite sym (ηmap₁ xs) = refl

ηmap₂ : ∀ {A B : Set} {f : A → B} (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
ηmap₂ [] ys = refl
ηmap₂ {f = f} (x ∷ xs) ys rewrite ηmap₂ {f = f} xs ys = refl

ηmap₃ : ∀ {A B C : Set} {g : B → C} {f} (xs : List A) → map g (map f xs) ≡ map (g ∘ f) xs
ηmap₃ [] = refl
ηmap₃ {g = g} {f = f} (x ∷ xs) rewrite ηmap₃ {g = g} {f = f} xs = refl

ηfold₁ : ∀ {A B : Set} {c} {n : B} (xs ys : List A) →
  foldr c n (xs ++ ys) ≡ foldr c (foldr c n ys) xs
ηfold₁ [] ys = refl
ηfold₁ {c = c} {n = n} (x ∷ xs) ys rewrite ηfold₁ {c = c} {n = n} xs ys = refl

ηfold₂ : ∀ {A B C : Set} {c} {n : C} {f : A → B} (xs : List A) →
  foldr c n (map f xs) ≡ foldr (c ∘ f) n xs
ηfold₂ [] = refl
ηfold₂ {c = c} {n = n} {f = f} (x ∷ xs) rewrite ηfold₂ {c = c} {n = n} {f = f} xs = refl

η++₁ : ∀ {A : Set} (xs : List A) → xs ≡ xs ++ []
η++₁ [] = refl
η++₁ (x ∷ xs) rewrite sym (η++₁ xs) = refl

η++₂ : ∀ {A : Set} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
η++₂ [] ys zs = refl
η++₂ (x ∷ xs) ys zs rewrite η++₂ xs ys zs = refl

{- interpreting a term with a substitution applied is the same as
   interpreting this term in a the interpretation of the substitution. -}

lookup-subst : ∀ {n Γ Δ} {σ : ty n} (pr : σ ∈ Γ) (r : Δ ⊢ε Γ) {ρ} (R : ⟦ Δ ⟧ε ρ) →
  ⌈ get pr r ⌉ R ≡ lookup pr (⌈ Γ ! r ⌉ε R)
lookup-subst here!      (_ , rσ) R = refl
lookup-subst (there pr) (rΓ , _) R = lookup-subst pr rΓ R

interp-subst : ∀ {n Γ Δ} {σ : ty n} (t : Γ ⊢ σ) (r : Δ ⊢ε Γ) {ρ} (R : ⟦ Δ ⟧ε ρ) →
  ⌈ subst t r ⌉ R ≡ ⌈ t ⌉ (⌈ Γ ! r ⌉ε R)
interp-subst (`v pr)        r R = lookup-subst pr r R
interp-subst {_} {Γ} {Δ} {σ `→ τ} (`λ t) r R = fun-ext (λ S →
  let eqt = interp-subst t (⊢ε-weaken Γ (step (same Δ)) r , `v here!) (R , S)
      eqΓ = interpε-purge Γ (step {σ = σ} (same Δ)) r (R , S)
  in  trans eqt (cong (λ R → ⌈ t ⌉ (R , S))
     (trans eqΓ (cong ⌈ Γ ! r ⌉ε (purge-refl Δ R))) ))
interp-subst (f `$ x)       r R = cong₂ _$_ (interp-subst f r R) (interp-subst x r R)
interp-subst `⟨⟩            r R = refl
interp-subst (a `, b)       r R = cong₂ _,_ (interp-subst a r R) (interp-subst b r R)
interp-subst (`π₁ t)        r R = cong proj₁ (interp-subst t r R)
interp-subst (`π₂ t)        r R = cong proj₂ (interp-subst t r R)
interp-subst `[]            r R = refl
interp-subst (hd `∷ tl)     r R = cong₂ _∷_ (interp-subst hd r R) (interp-subst tl r R)
interp-subst (xs `++ ys)    r R = cong₂ _++_ (interp-subst xs r R) (interp-subst ys r R)
interp-subst (`map f xs)    r R = cong₂ map (interp-subst f r R) (interp-subst xs r R)
interp-subst (`fold c n xs) r R =
  cong₃ foldr (interp-subst c r R) (interp-subst n r R) (interp-subst xs r R)

{- And now we can prove soundness of the reduction relation
   with respect to Agda's propositional equality. -}

soundness : ∀ {n Γ} {σ : ty n} {s t : Γ ⊢ σ} ρ R (r : Γ ⊢ σ ∋ s ↝ t) → ⌈ s ⌉ {ρ} R ≡ ⌈ t ⌉ R
soundness ρ R (`λ red) = fun-ext (λ S → soundness ρ (R , S) red)
soundness {s = f `$ x} ρ R (`$₁ red) = cong (λ f → f (⌈ x ⌉ R)) (soundness ρ R red)
soundness {s = f `$ x} ρ R (`$₂ red) = cong (⌈ f ⌉ R) (soundness ρ R red)
soundness {s = a `, b} ρ R (`,₁ red) = cong (λ a → a , ⌈ b ⌉ R) (soundness ρ R red)
soundness {s = a `, b} ρ R (`,₂ red) = cong (_,_ (⌈ a ⌉ R)) (soundness ρ R red)
soundness ρ R (`π₁ red) = cong proj₁ (soundness ρ R red)
soundness ρ R (`π₂ red) = cong proj₂ (soundness ρ R red)
soundness {s = hd `∷ tl} ρ R (`∷₁ red) = cong (λ hd → hd ∷ ⌈ tl ⌉ R) (soundness ρ R red)
soundness ρ R (`∷₂ red) = cong (_∷_ _) (soundness ρ R red)
soundness {s = xs `++ ys} ρ R (`++₁ red) = cong (λ xs → xs ++ ⌈ ys ⌉ R) (soundness ρ R red)
soundness {s = xs `++ ys} ρ R (`++₂ red) = cong (_++_ (⌈ xs ⌉ R)) (soundness ρ R red)
soundness {s = `map f xs} ρ R (`map₁ red) = cong (λ f → map f (⌈ xs ⌉ R)) (soundness ρ R red)
soundness ρ R (`map₂ red) = cong (map _) (soundness ρ R red)
soundness {s = `fold c n xs} ρ R (`fold₁ red) =
  cong (λ c → foldr c (⌈ n ⌉ R) (⌈ xs ⌉ R)) (soundness ρ R red)
soundness {s = `fold c n xs} ρ R (`fold₂ red) =
  cong (λ n → foldr (⌈ c ⌉ R) n (⌈ xs ⌉ R)) (soundness ρ R red)
soundness {s = `fold c n xs} ρ R (`fold₃ red) =
  cong (foldr (⌈ c ⌉ R) (⌈ n ⌉ R)) (soundness ρ R red)
soundness {Γ = Γ} {s = `λ b `$ x} ρ R `βλ =
  let eq = sym (interp-subst b (⊢ε-refl Γ , x) R)
  in trans (cong (λ B → ⌈ b ⌉ (B , ⌈ x ⌉ R)) (sym (interp-⊢ε-refl Γ R))) eq
soundness ρ R `βπ₁             = refl
soundness ρ R `βπ₂             = refl
soundness ρ R `β++₁            = refl
soundness ρ R `β++₂            = refl
soundness ρ R `βmap₁           = refl
soundness ρ R `βmap₂           = refl
soundness ρ R `βfold₁          = refl
soundness ρ R `βfold₂          = refl
soundness {Γ = Γ} {σ = σ `→ τ} ρ R (`ηλ f) = fun-ext (λ S →
  let eqf = interp-purge (step {σ = σ} (same Γ)) f (R , S)
  in sym (cong (λ f → f S) (trans eqf (cong ⌈ f ⌉ (purge-refl Γ R)))))
soundness ρ R (`η× p)          = refl
soundness ρ R (`η1 t)          = refl
soundness ρ R (`ηmap₁ xs)      = ηmap₁ (⌈ xs ⌉ R)
soundness ρ R (`ηmap₂ xs ys)   = ηmap₂ (⌈ xs ⌉ R) (⌈ ys ⌉ R)
soundness ρ R (`ηmap₃ g f xs)  =
  trans (ηmap₃ (⌈ xs ⌉ R)) (cong (λ f → map f (⌈ xs ⌉ R)) (sym (comp g f ρ R)))
soundness ρ R (`ηfold₁ xs ys)  = ηfold₁ (⌈ xs ⌉ R) (⌈ ys ⌉ R)
soundness {s = `fold .c n .(`map f xs)} ρ R (`ηfold₂ c f xs) =
  trans (ηfold₂ (⌈ xs ⌉ R)) (cong (λ c → foldr c (⌈ n ⌉ R) (⌈ xs ⌉ R)) (sym (comp c f ρ R)))
soundness ρ R (`η++₁ xs)       = η++₁ (⌈ xs ⌉ R)
soundness ρ R (`η++₂ xs ys zs) = η++₂ (⌈ xs ⌉ R) (⌈ ys ⌉ R) (⌈ zs ⌉ R)

soundness' : ∀ {n Γ} {σ : ty n} {s t : Γ ⊢ σ} {ρ R} (r : Γ ⊢ σ ∋ s ≅ t) → ⌈ s ⌉ {ρ} R ≡ ⌈ t ⌉ R
soundness' refl        = refl
soundness' (lstep p r) = trans      (soundness _ _ p)  (soundness' r)
soundness' (rstep p r) = trans (sym (soundness _ _ p)) (soundness' r)

dec-cast : ∀ {A : Set} (a : Dec A) → Set
dec-cast (yes a) = ⊤
dec-cast (no ¬a) = ⊥

solve : ∀ {n Γ} {σ : ty n} (s t : Γ ⊢ σ) ρ (R : ⟦ Γ ⟧ε ρ)
  {_ : dec-cast (≅-dec s t)} → ⌈ s ⌉ R ≡ ⌈ t ⌉ R
solve s t ρ R {b} with ≅-dec s t
... | yes red = soundness' red
... | no ¬red = ⊥-elim b

{- Examples -}

open import Data.Fin

swap : ∀ {A B : Set} → A × B → B × A
swap (a , b) = b , a

teswap : ∀ {n Γ} (k₁ k₂ : Fin n) → Γ ⊢ `b k₁ `× `b k₂ `→ `b k₂ `× `b k₁
teswap k₁ k₂ = `λ (`π₂ (`v here!) `, `π₁ (`v here!))

eq-swap : ∀ {A B : Set} → swap ≡ ⌈ teswap zero (suc zero) ⌉ {ρ = A Vec.∷ B Vec.∷ Vec.[]} tt
eq-swap = refl

lemma : ∀ {A : Set} (xs : List (A × A)) → map swap (map swap xs) ≡ xs
lemma {A} xs =
  solve (`map (teswap zero zero) (`map (teswap zero zero) (`v here!))) (`v here!)
   (A Vec.∷ Vec.[]) (tt , xs)