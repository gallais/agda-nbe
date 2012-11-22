module stlcl.simple.sound where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (subst to coerce ; subst₂ to coerce₂)

open import tools.contexts
open import tools.closures

open import stlcl.definition
open import stlcl.reductions
open import stlcl.normalforms
open import stlcl.simple.model
open import stlcl.simple.eval

infix 2 [_⊩list_]_↯_ [_⊩_]_↯_ [_⊩ε_]_↯_ [_]_↯↓ne [_]_↝⋆↑_when_ 

data [_⊩list_]_↯_ {n} Γ {σ : ty n} {Σ : ∀ Δ → Set} (Σ↯ : ∀ Δ (t : Δ ⊢ σ) (T : Σ Δ) → Set)
  (t : Γ ⊢ `list σ) : (T : Γ ⊩list Σ) → Set where
  `[] : (red : Γ ⊢ `list σ ∋ t ↝⋆ `[]) → [ Γ ⊩list Σ↯ ] t ↯ `[]
  _`∷_by_ : ∀ {hd HD} (rhd : Σ↯ Γ hd HD) {tl TL} (rtl : [ Γ ⊩list Σ↯ ] tl ↯ TL)
    (red : Γ ⊢ `list σ ∋ t ↝⋆ hd `∷ tl) → [ Γ ⊩list Σ↯ ] t ↯ HD `∷ TL
  mappend : ∀ {τ} {f} {F : ∀ {Δ} (inc : Γ ⊆ Δ) (t : Δ ⊢ne τ) → Σ Δ}
    (rf : ∀ {Δ} (inc : Γ ⊆ Δ) (t : Δ ⊢ne τ) → Σ↯ Δ (⊢-weaken inc f `$ back-ne t) (F {Δ} inc t))
    (xs : Γ ⊢ne `list τ) {ys YS} (rys : [ Γ ⊩list Σ↯ ] ys ↯ YS)
    (red : Γ ⊢ `list σ ∋ t ↝⋆ `map f (back-ne xs) `++ ys) →
    [ Γ ⊩list Σ↯ ] t ↯ mappend F xs YS

[_⊩_]_↯_ : ∀ {n} Γ (σ : ty n) (t : Γ ⊢ σ) (T : Γ ⊩ σ) → Set
[ Γ ⊩ `1 ] t ↯ T = ⊤
[ Γ ⊩ `b k ] t ↯ T = Γ ⊢ `b k ∋ t ↝⋆ back-ne T
[ Γ ⊩ σ `× τ ] t ↯ A , B =
  Σ[ a ∶ Γ ⊢ σ ] Σ[ b ∶ Γ ⊢ τ ]
  Γ ⊢ σ `× τ ∋ t ↝⋆ a `, b ×
  [ Γ ⊩ σ ] a ↯ A ×
  [ Γ ⊩ τ ] b ↯ B
[ Γ ⊩ σ `→ τ ] f ↯ F =
  ∀ {Δ} (inc : Γ ⊆ Δ) {x X} (rx : [ Δ ⊩ σ ] x ↯ X)
  {fx} (red : Δ ⊢ τ ∋ fx ↝⋆ ⊢-weaken inc f `$ x) →
  [ Δ ⊩ τ ] fx ↯ F inc X 
[ Γ ⊩ `list σ ] t ↯ T = [ Γ ⊩list (λ Γ t T → [ Γ ⊩ σ ] t ↯ T) ] t ↯ T

[_⊩ε_]_↯_ : ∀ {n} (Δ Γ : Con (ty n)) (ρ : Δ ⊢ε Γ) (T : Δ ⊩ε Γ) → Set
[ Δ ⊩ε ε ] ρ ↯ T = ⊤
[ Δ ⊩ε Γ ∙ σ ] ρ , r ↯ T , t = [ Δ ⊩ε Γ ] ρ ↯ T × [ Δ ⊩ σ ] r ↯ t

{- weakening -}

mutual

  abstract

    ↯list-weaken : ∀ {n Γ} (σ : ty n) {Δ} (inc : Γ ⊆ Δ) {t T} (r : [ Γ ⊩ `list σ ] t ↯ T) →
      [ Δ ⊩ `list σ ] ⊢-weaken inc t ↯ ⊩-weaken (`list σ) inc T
    ↯list-weaken σ inc (`[] red) = `[] (↝⋆-weaken inc red)
    ↯list-weaken σ inc (rhd `∷ rtl by red) =
      ↯-weaken σ inc rhd `∷ ↯list-weaken σ inc rtl by ↝⋆-weaken inc red
    ↯list-weaken σ {Δ} inc {t} (mappend {τ} {f} {F} rf xs {ys} rys red) =
      mappend (λ {Ε} inc' t → coerce (λ f → [ Ε ⊩ σ ] f `$ back-ne t ↯ F (⊆-trans inc inc') t)
        (sym (⊢-weaken² inc inc' f)) (rf (⊆-trans inc inc') t))
      (ne-weaken inc xs) (↯list-weaken σ inc rys)
      (Proof[ Δ ⊢ `list σ ]
         Δ ⊢ `list σ ∋ ⊢-weaken inc t
         ↝⋆⟨ ↝⋆-weaken inc red ⟩
         Δ ⊢ `list σ ∋ `map (⊢-weaken inc f) (⊢-weaken inc (back-ne xs)) `++ ⊢-weaken inc ys
         ≡⟨ cong (λ xs → `map (⊢-weaken inc f) xs `++ ⊢-weaken inc ys)
           (sym (ne-weaken-back inc xs)) ⟩
         Δ ⊢ `list σ ∋ `map (⊢-weaken inc f) (back-ne (ne-weaken inc xs)) `++ ⊢-weaken inc ys
       Qed)

    ↯-weaken : ∀ {n Γ} (σ : ty n) {Δ} (inc : Γ ⊆ Δ) {t T} (r : [ Γ ⊩ σ ] t ↯ T) →
      [ Δ ⊩ σ ] ⊢-weaken inc t ↯ ⊩-weaken σ inc T
    ↯-weaken `1 inc r = r
    ↯-weaken (`b k) {Δ} inc {t} {T} r =
      Proof[ Δ ⊢ `b k ]
        Δ ⊢ `b k ∋ ⊢-weaken inc t
        ↝⋆⟨ ↝⋆-weaken inc r ⟩
        Δ ⊢ `b k ∋ ⊢-weaken inc (back-ne T)
        ≡⟨ sym (ne-weaken-back inc T) ⟩
        Δ ⊢ `b k ∋ back-ne (ne-weaken inc T)
      Qed
    ↯-weaken (σ `× τ) inc (a , b , red , ra , rb) =
      ⊢-weaken inc a ,
      ⊢-weaken inc b ,
      ↝⋆-weaken inc red ,
      ↯-weaken σ inc ra ,
      ↯-weaken τ inc rb
    ↯-weaken (σ `→ τ) inc r =
      λ {Ε} inc' {x} {X} rx {fx} red →
      r (⊆-trans inc inc') rx (coerce (λ t → Ε ⊢ τ ∋ fx ↝⋆ t `$ x) (⊢-weaken² inc inc' _) red)
    ↯-weaken (`list σ) inc r = ↯list-weaken σ inc r

abstract

  ↯ε-weaken : ∀ {n Δ} (Γ : Con (ty n)) {Ε} (inc : Δ ⊆ Ε) {ρ R} (rR : [ Δ ⊩ε Γ ] ρ ↯ R) →
      [ Ε ⊩ε Γ ] ⊢ε-weaken Γ inc ρ ↯ ⊩ε-weaken Γ inc R
  ↯ε-weaken ε inc rR = rR
  ↯ε-weaken (Γ ∙ σ) inc (rR , rr) = ↯ε-weaken Γ inc rR , ↯-weaken σ inc rr

{- [ Γ ⊩ σ ] t ↯ T is upward close with respect to ↝⋆ -}

mutual

  abstract

    ↯list-upward : ∀ {n Γ} (σ : ty n) {s t} (red : Γ ⊢ `list σ ∋ s ↝⋆ t)
      {T} (r : [ Γ ⊩ `list σ ] t ↯ T) → [ Γ ⊩ `list σ ] s ↯ T
    ↯list-upward σ red (`[] r) = `[] (▹⋆-trans red r)
    ↯list-upward σ red (rhd `∷ rtl by r) = rhd `∷ rtl by (▹⋆-trans red r)
    ↯list-upward σ red (mappend rf xs rys r) = mappend rf xs rys (▹⋆-trans red r)

    ↯-upward : ∀ {n Γ} (σ : ty n) {s t} (red : Γ ⊢ σ ∋ s ↝⋆ t)
      {T} (r : [ Γ ⊩ σ ] t ↯ T) → [ Γ ⊩ σ ] s ↯ T
    ↯-upward `1 red r = r
    ↯-upward (`b k) red r = ▹⋆-trans red r
    ↯-upward (σ `× τ) red (a , b , r , rab) = a , b , ▹⋆-trans red r , rab
    ↯-upward (σ `→ τ) red r =
      λ inc rx rfx → r inc rx (▹⋆-trans rfx (▹⋆-cong `$₁ (↝⋆-weaken inc red)))
    ↯-upward (`list σ) red r = ↯list-upward σ red r

mutual

  abstract

    [_]_↯↓ne : ∀ {n Γ} (σ : ty n) (t : Γ ⊢ne σ) → [ Γ ⊩ σ ] back-ne t ↯ ↓[ σ ] t
    [ `1 ] t ↯↓ne = tt
    [ `b k ] t ↯↓ne = refl
    [ σ `× τ ] t ↯↓ne =
      `π₁ (back-ne t) ,
      `π₂ (back-ne t) ,
      step (`η× (back-ne t)) refl ,
      [ σ ] `π₁ t ↯↓ne ,
      [ τ ] `π₂ t ↯↓ne
    [ σ `→ τ ] t ↯↓ne =
      λ {Δ} inc {x} {X} rx {fx} red →
      ↯-upward τ
      (▹⋆-trans red (≡-step (cong (λ f → f `$ x) (sym (ne-weaken-back inc t)))
        (▹⋆-cong `$₂ ([ σ ] x ↝⋆↑ X when rx))))
      [ τ ] ne-weaken inc t `$ ↑[ σ ] X ↯↓ne
    [ `list σ ] t ↯↓ne =
      mappend (λ {Δ} inc x → ↯-upward σ (step `βλ refl) [ σ ] x ↯↓ne) t (`[] refl)
      (step (`ηmap₁ (back-ne t)) (step (`η++₁ (`map (`λ (`v here!)) (back-ne t))) refl))

    [_]_↝⋆↑list_when_ : ∀ {n Γ} (σ : ty n) (t : Γ ⊢ `list σ) (T : Γ ⊩ `list σ)
      (r : [ Γ ⊩ `list σ ] t ↯ T) → Γ ⊢ `list σ ∋ t ↝⋆ back-nf (↑[ `list σ ] T)
    [ σ ] t ↝⋆↑list `[] when `[] red = red
    [ σ ] t ↝⋆↑list HD `∷ TL when (rhd `∷ rtl by red) =
      ▹⋆-trans red (▹⋆-trans (▹⋆-cong `∷₁ ([ σ ] _ ↝⋆↑ HD when rhd))
      (▹⋆-cong `∷₂ ([ σ ] _ ↝⋆↑list TL when rtl)))
    [ σ ] t ↝⋆↑list mappend F xs YS when (mappend {τ} {f} rf .xs {ys} rys red) =
      Proof[ _ ⊢ `list σ ]
        _ ⊢ `list σ ∋ t
        ↝⋆⟨ red ⟩
        _ ⊢ `list σ ∋ `map f (back-ne xs) `++ ys
        ↝⟨ `++₁ (`map₁ (`ηλ f)) ⟩
        _ ⊢ `list σ ∋ `map (`λ (⊢-weaken (step (same _)) f `$ `v here!)) (back-ne xs) `++ ys
        ↝⋆⟨ ▹⋆-cong {f = λ f → `map (`λ f) (back-ne xs) `++ ys} (λ p → `++₁ (`map₁ (`λ p)))
            ([ σ ] _ ↝⋆↑ _ when (rf (step (same _)) (`v here!))) ⟩
        _ ⊢ `list σ ∋ `map (`λ (back-nf (↑[ σ ] F (step (same _)) (`v here!)))) (back-ne xs) `++ ys
        ↝⋆⟨ ▹⋆-cong `++₂ ([ σ ] ys ↝⋆↑list YS when rys) ⟩
        _ ⊢ `list σ ∋ `map (`λ (back-nf (↑[ σ ] F (step (same _)) (`v here!)))) (back-ne xs)
                      `++ back-nf (↑[ `list σ ] YS)
      Qed

    [_]_↝⋆↑_when_ : ∀ {n Γ} (σ : ty n) (t : Γ ⊢ σ) (T : Γ ⊩ σ) (r : [ Γ ⊩ σ ] t ↯ T) →
      Γ ⊢ σ ∋ t ↝⋆ back-nf (↑[ σ ] T)
    [ `1 ] t ↝⋆↑ T when r = step (`η1 t) refl
    [ `b k ] t ↝⋆↑ T when r = r
    [ σ `× τ ] t ↝⋆↑ A , B when (a , b , red , ra , rb) =
      Proof[ _ ⊢ σ `× τ ]
        _ ⊢ σ `× τ ∋ t
        ↝⋆⟨ red ⟩
        _ ⊢ σ `× τ ∋ a `, b
        ↝⋆⟨ ▹⋆-cong `,₁ ([ σ ] a ↝⋆↑ A when ra) ⟩
        _ ⊢ σ `× τ ∋ back-nf (↑[ σ ] A) `, b
        ↝⋆⟨ ▹⋆-cong `,₂ ([ τ ] b ↝⋆↑ B when rb) ⟩
        _ ⊢ σ `× τ ∋ back-nf (↑[ σ ] A) `, back-nf (↑[ τ ] B)
      Qed
    [ σ `→ τ ] t ↝⋆↑ T when r =
      step (`ηλ t) (▹⋆-cong {f = `λ} `λ
      ([ τ ] ⊢-weaken (step (same _)) t `$ `v here! ↝⋆↑ T (step (same _)) (↓[ σ ] `v here!)
      when r (step (same _)) [ σ ] `v here! ↯↓ne refl))
    [ `list σ ] t ↝⋆↑ T when r = [ σ ] t ↝⋆↑list T when r

abstract

  ↯ε-refl : ∀ {n} (Γ : Con (ty n)) → [ Γ ⊩ε Γ ] ⊢ε-refl Γ ↯ ⊩ε-refl Γ
  ↯ε-refl ε = tt
  ↯ε-refl (Γ ∙ σ) = ↯ε-weaken Γ (step (same Γ)) (↯ε-refl Γ) , [ σ ] `v here! ↯↓ne

abstract

  get-↯ : ∀ {n Γ} (σ : ty n) (pr : σ ∈ Γ) {Δ ρ R} (cR : [ Δ ⊩ε Γ ] ρ ↯ R) →
    [ Δ ⊩ σ ] get pr ρ ↯ lookup Γ pr R
  get-↯ σ here! (_ , cr) = cr
  get-↯ σ (there pr) (cR , _) = get-↯ σ pr cR

  vappend-↯ : ∀ {n Γ} (σ : ty n) {xs XS} (rxs : [ Γ ⊩ `list σ ] xs ↯ XS)
    {ys YS} (rys : [ Γ ⊩ `list σ ] ys ↯ YS) → [ Γ ⊩ `list σ ] xs `++ ys ↯ vappend σ XS YS
  vappend-↯ σ (`[] red) rys = ↯-upward (`list σ) (▹⋆-trans (▹⋆-cong `++₁ red) (step `β++₁ refl)) rys
  vappend-↯ σ (rhd `∷ rtl by red) rys =
    rhd `∷ vappend-↯ σ rtl rys by ▹⋆-trans (▹⋆-cong `++₁ red) (step `β++₂ refl)
  vappend-↯ σ (mappend {τ} {f} rf xs {ys} rys red) {zs} rzs =
    mappend rf xs (vappend-↯ σ rys rzs) (▹⋆-trans (▹⋆-cong `++₁ red)
    (step (`η++₂ (`map f (back-ne xs)) ys zs) refl))

  vmap-↯ : ∀ {n Γ} (σ τ : ty n) {f} {F : Γ ⊩ σ `→ τ} (rf : [ Γ ⊩ σ `→ τ ] f ↯ F)
    {xs XS} (rxs : [ Γ ⊩ `list σ ] xs ↯ XS) → [ Γ ⊩ `list τ ] `map f xs ↯ vmap σ τ F XS
  vmap-↯ σ τ rf (`[] red) = `[] (▹⋆-trans (▹⋆-cong `map₂ red) (step `βmap₁ refl))
  vmap-↯ {Γ = Γ} σ τ {f} rf (_`∷_by_ {hd} rhd {tl} rtl red) =
    rf (same Γ) rhd refl `∷ vmap-↯ σ τ rf rtl by
    ▹⋆-trans (▹⋆-cong `map₂ red) (step `βmap₂
   (≡-step (cong (λ g → (g `$ hd) `∷ `map f tl) (sym (⊢-weaken-refl f))) refl))
  vmap-↯ {Γ = Γ} σ τ {f} rf (mappend {υ} {g} rg xs {ys} rys red) =
    mappend
    (λ {Δ} inc t → rf inc (rg inc t)
    (Proof[ Δ ⊢ τ ]
      Δ ⊢ τ ∋ _
      ≡⟨ cong₂ (λ f' g' → `λ (f' `$ (g' `$ `v here!)) `$ back-ne t)
         (⊢-weaken² (step (same Γ)) (pop! inc) f) (⊢-weaken² (step (same Γ)) (pop! inc) g) ⟩
      Δ ⊢ τ ∋ _
      ≡⟨ cong (λ pr → `λ (⊢-weaken pr f `$ (⊢-weaken pr g `$ `v here!)) `$ back-ne t)
         (cong step (⊆-same-l inc)) ⟩
      Δ ⊢ τ ∋ `λ (⊢-weaken (step inc) f `$ (⊢-weaken (step inc) g `$ `v here!)) `$ back-ne t
      ↝⟨ `βλ ⟩
      Δ ⊢ τ ∋ _
      ≡⟨ cong₂ (λ f' g' → f' `$ (g' `$ back-ne t))
        (trans (subst-weaken (step inc) f (⊢ε-refl Δ , back-ne t))
           (trans (cong (subst f) (purge-⊢ε-refl inc)) (sym (weaken-subst inc f (⊢ε-refl Γ)))))
        (trans (subst-weaken (step inc) g (⊢ε-refl Δ , back-ne t))
           (trans (cong (subst g) (purge-⊢ε-refl inc)) (sym (weaken-subst inc g (⊢ε-refl Γ))))) ⟩
      Δ ⊢ τ ∋ ⊢-weaken inc (subst f (⊢ε-refl Γ)) `$ (⊢-weaken inc (subst g (⊢ε-refl Γ)) `$ back-ne t)
      ≡⟨ cong₂ (λ f' g' → ⊢-weaken inc f' `$ (⊢-weaken inc g' `$ back-ne t))
           (subst-refl f) (subst-refl g)  ⟩
      Δ ⊢ τ ∋ ⊢-weaken inc f `$ (⊢-weaken inc g `$ back-ne t)
    Qed))
    xs (vmap-↯ σ τ rf rys)
    (▹⋆-trans (▹⋆-cong `map₂ red) (step (`ηmap₂ (`map g (back-ne xs)) ys)
    (step (`++₁ (`ηmap₃ f g (back-ne xs))) refl)))

  vfold-↯ : ∀ {n Γ} (σ τ : ty n) {c} {C : Γ ⊩ σ `→ τ `→ τ} (rc : [ Γ ⊩ σ `→ τ `→ τ ] c ↯ C)
    {n N} (rn : [ Γ ⊩ τ ] n ↯ N) {xs XS} (rxs : [ Γ ⊩ `list σ ] xs ↯ XS) →
    [ Γ ⊩ τ ] `fold c n xs ↯ vfold σ τ C N XS
  vfold-↯ σ τ rc rn (`[] red) =
    ↯-upward τ (▹⋆-trans (▹⋆-cong `fold₃ red) (step `βfold₁ refl)) rn
  vfold-↯ {Γ = Γ} σ τ {c} rc {n} rn (_`∷_by_ {hd} rhd {tl} rtl red) =
    rc (same Γ) rhd (≡-step (sym (cong (λ f → f `$ hd) (⊢-weaken-refl c))) refl)
    (same Γ) (vfold-↯ σ τ rc rn rtl) (▹⋆-trans (▹⋆-cong `fold₃ red) (step `βfold₂
    (≡-step (cong₂ (λ c' hd' → c' `$ hd' `$ `fold c n _) (sym (⊢-weaken-refl c))
    (sym (⊢-weaken-refl hd))) refl)))
  vfold-↯ {Γ = Γ} σ τ {c} rc {n} rn {xs} (mappend {υ} {f} rf ys {zs} rzs red) =
    ↯-upward τ
    (Proof[ Γ ⊢ τ ]
      Γ ⊢ τ ∋ `fold c n xs
      ↝⋆⟨ ▹⋆-cong `fold₃ red ⟩
      Γ ⊢ τ ∋ `fold c n (`map f (back-ne ys) `++ zs)
      ↝⟨ `ηfold₁ (`map f (back-ne ys)) zs ⟩
      Γ ⊢ τ ∋ `fold c (`fold c n zs) (`map f (back-ne ys))
      ↝⟨ `ηfold₂ c f (back-ne ys) ⟩
      Γ ⊢ τ ∋ `fold (c `∘ f) (`fold c n zs) (back-ne ys)
      ↝⟨ `fold₁ (`λ (`ηλ _)) ⟩
      Γ ⊢ τ ∋ _
      ↝⋆⟨ ▹⋆-cong {f = λ cf → `fold (`λ (`λ cf)) (`fold c n zs) (back-ne ys)}
          (λ p → `fold₁ (`λ (`λ p)))
          ([ τ ] _ ↝⋆↑ _ when rc (step (step (same Γ))) (rf (step (step (same Γ)))
          (`v (there here!))) refl (same _) [ τ ] `v here! ↯↓ne
          (≡-step (cong₂ (λ c' f' → c' `$ (f' `$ `v (there here!)) `$ `v here!)
          (trans (⊢-weaken² _ _ c) (sym (⊢-weaken² _ _ c)))
          (trans (⊢-weaken² _ _ f) (sym (⊢-weaken² _ _ f)))) refl)) ⟩
      Γ ⊢ τ ∋ _
      ↝⋆⟨ ▹⋆-cong `fold₂ ([ τ ] _ ↝⋆↑ _ when vfold-↯ σ τ rc rn rzs) ⟩
      Γ ⊢ τ ∋ _
    Qed)
    [ τ ] _ ↯↓ne

  eval-↯ : ∀ {n Γ} (σ : ty n) (t : Γ ⊢ σ) {Δ ρ R} (cR : [ Δ ⊩ε Γ ] ρ ↯ R) →
    [ Δ ⊩ σ ] subst t ρ ↯ eval t R
  eval-↯ σ (`v pr) cR = get-↯ σ pr cR
  eval-↯ {Γ = Γ} (σ `→ τ) (`λ t) {Δ} {ρ} {R} cR =
    λ {Ε} inc {x} {X} rx {fx} red →
    let ρ' = ⊢ε-weaken Γ (step (same Δ)) ρ in
    ↯-upward τ
    (Proof[ Ε ⊢ τ ]
      Ε ⊢ τ ∋ fx
      ↝⋆⟨ red ⟩
      Ε ⊢ τ ∋ `λ (⊢-weaken (pop! inc) (subst t (ρ' , `v here!))) `$ x
      ≡⟨ cong (λ f → `λ f `$ x) (weaken-subst (pop! inc) t (ρ' , `v here!)) ⟩
      Ε ⊢ τ ∋ `λ (subst t (⊢ε-weaken Γ (pop! inc) ρ' , `v here!)) `$ x
      ≡⟨ cong (λ ρ → `λ (subst t (ρ , `v here!)) `$ x)
        (trans (⊢ε-weaken² Γ (step (same Δ)) (pop! inc) ρ)
        (cong (λ pr → ⊢ε-weaken Γ (step pr) ρ) (⊆-same-l inc))) ⟩
      Ε ⊢ τ ∋ `λ (subst t (⊢ε-weaken Γ (step inc) ρ , `v here!)) `$ x
      ↝⟨ `βλ ⟩
      Ε ⊢ τ ∋ subst (subst t (⊢ε-weaken Γ (step inc) ρ , `v here!)) (⊢ε-refl Ε , x)
      ≡⟨ subst² t (⊢ε-weaken Γ (step inc) ρ , `v here!) (⊢ε-refl Ε , x) ⟩
      Ε ⊢ τ ∋ subst t (⊢ε² Γ (⊢ε-weaken Γ (step inc) ρ) (⊢ε-refl Ε , x) , x)
      ≡⟨ cong (λ ρ → subst t (ρ , x)) (trans (⊢ε²-step Γ inc ρ (⊢ε-refl Ε) x)
         (⊢ε²-refl Γ (⊢ε-weaken Γ inc ρ))) ⟩
      Ε ⊢ τ ∋ subst t (⊢ε-weaken Γ inc ρ , x)
    Qed)
    (eval-↯ τ t (↯ε-weaken Γ inc cR , rx))
  eval-↯ {Γ = Γ} τ (_`$_ {σ} t u) {Δ} {ρ} {R} cR =
    eval-↯ (σ `→ τ) t cR (same Δ) (eval-↯ σ u cR)
    (Proof[ Δ ⊢ τ ]
       Δ ⊢ τ ∋ subst t ρ `$ subst u ρ
       ≡⟨ cong (λ t → t `$ subst u ρ) (sym (⊢-weaken-refl (subst t ρ))) ⟩
       Δ ⊢ τ ∋ ⊢-weaken (⊆-refl Δ) (subst t ρ) `$ subst u ρ
    Qed)
  eval-↯ .`1 `⟨⟩ cR = tt
  eval-↯ .(σ `× τ) (_`,_ {σ} {τ} a b) {Δ} {ρ} {R} cR =
    subst a ρ ,
    subst b ρ ,
    refl ,
    eval-↯ σ a cR ,
    eval-↯ τ b cR
  eval-↯ σ (`π₁ {.σ} {τ} p) cR with eval-↯ (σ `× τ) p cR
  ... | a , b , red , ra , rb = ↯-upward σ (▹⋆-trans (▹⋆-cong `π₁ red) (step `βπ₁ refl)) ra
  eval-↯ τ (`π₂ {σ} p) cR with eval-↯ (σ `× τ) p cR
  ... | a , b , red , ra , rb = ↯-upward τ (▹⋆-trans (▹⋆-cong `π₂ red) (step `βπ₂ refl)) rb
  eval-↯ .(`list σ) (`[] {σ}) cR = `[] refl
  eval-↯ (`list σ) (hd `∷ tl) cR =
    eval-↯ σ hd cR `∷ eval-↯ (`list σ) tl cR by refl
  eval-↯ (`list σ) (xs `++ ys) cR = vappend-↯ σ (eval-↯ (`list σ) xs cR) (eval-↯ (`list σ) ys cR)
  eval-↯ .(`list τ) (`map {σ} {τ} f xs) cR =
    vmap-↯ σ τ (eval-↯ (σ `→ τ) f cR) (eval-↯ (`list σ) xs cR)
  eval-↯ τ (`fold {σ} c n xs) cR =
    vfold-↯ σ τ (eval-↯ (σ `→ τ `→ τ) c cR) (eval-↯ τ n cR) (eval-↯ (`list σ) xs cR)

abstract

  ↝⋆-norm : ∀ {n Γ} {σ : ty n} (t : Γ ⊢ σ) → Γ ⊢ σ ∋ t ↝⋆ norm t
  ↝⋆-norm {_} {Γ} {σ} t =
    Proof[ Γ ⊢ σ ]
      Γ ⊢ σ ∋ t
      ≡⟨ sym (subst-refl t) ⟩
      Γ ⊢ σ ∋ subst t (⊢ε-refl Γ)
      ↝⋆⟨  [ σ ] subst t (⊢ε-refl Γ) ↝⋆↑ eval t (⊩ε-refl Γ) when eval-↯ σ t (↯ε-refl Γ) ⟩
      Γ ⊢ σ ∋ norm t
    Qed

  soundness : ∀ {n Γ} {σ : ty n} {s t : Γ ⊢ σ} (eq : norm s ≡ norm t) → Γ ⊢ σ ∋ s ≅ t
  soundness {s = s} {t = t} eq =
    ≡⋆-trans (▹≡⋆ (↝⋆-norm s))
   (≡⋆-step eq
   (≡⋆-sym (▹≡⋆ (↝⋆-norm t))))