module stlcl.simple.complete where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (subst to coerce ; subst₂ to coerce₂)

open import tools.closures
open import tools.contexts
open import stlcl.definition
open import stlcl.reductions
open import stlcl.normalforms
open import stlcl.simple.model
open import stlcl.simple.eval
open import stlcl.simple.equality

abstract

  Uni-comp : ∀ {n Γ} (σ τ υ : ty n) {G : Γ ⊩ τ `→ υ} (Guni : Uni[ τ `→ υ ] G)
    {F : Γ ⊩ σ `→ τ} (Funi : Uni[ σ `→ τ ] F) → Uni[ σ `→ υ ] (λ inc S → G inc (F inc S))
  Uni-comp σ τ υ {G} (g₁ , g₂ , g₃) {F} (f₁ , f₂ , f₃) =
    (λ inc S Suni → g₁ inc (F inc S) (f₁ inc S Suni)) ,
    (λ inc Suni₁ Suni₂ eqS₁S₂ → g₂ inc (f₁ inc _ Suni₁) (f₁ inc _ Suni₂) (f₂ inc Suni₁ Suni₂ eqS₁S₂)) ,
    (λ {Δ} {Ε} i₁ i₂ S Suni →
    Begin[ Ε ⊩ υ ]
      Ε ⊩ υ ∋ ⊩-weaken υ i₁ (G i₂ (F i₂ S))
      ≣⟨ g₃ i₁ i₂ (F i₂ S) (f₁ i₂ S Suni) ⟩
      Ε ⊩ υ ∋ G (⊆-trans i₂ i₁) (⊩-weaken τ i₁ (F i₂ S))
      ≣⟨ g₂ (⊆-trans i₂ i₁) (Uni-weaken τ i₁ (f₁ i₂ S Suni))
        (f₁ (⊆-trans i₂ i₁) _ (Uni-weaken σ i₁ Suni)) (f₃ i₁ i₂ S Suni) ⟩
      Ε ⊩ υ ∋ G (⊆-trans i₂ i₁) (F (⊆-trans i₂ i₁) (⊩-weaken σ i₁ S))
    Qed)

abstract

  eval-comp : ∀ {n Γ} (σ τ υ : ty n) (f : Γ ⊢ σ `→ τ) (g : Γ ⊢ τ `→ υ) {Δ} {R : Δ ⊩ε Γ}
    (Runi : Uni[ Γ ]ε R) → [ σ `→ υ ] eval (g `∘ f) R ≣ λ inc t → eval g R inc (eval f R inc t)
  eval-comp {Γ = Γ} σ τ υ f g {Δ} {R} Runi {Ε} inc S Suni =
    let Runi' = Uniε-weaken Γ inc Runi
        Funi = Uni-eval f Runi' in
    Begin[ Ε ⊩ υ ]
      Ε ⊩ υ ∋ _
      ≣⟨ eval-weaken g (step (⊆-refl Γ)) (Runi' , Suni) (⊆-refl Ε) _
         (proj₁ (Uni-eval (⊢-weaken (step (same Γ)) f) (Runi' , Suni)) (same Ε) S Suni) ⟩
      Ε ⊩ υ ∋ _
      ≣⟨ (let Runi'' = Uniε-purge (same Γ) Runi' in
         proj₁ (proj₂ (Uni-eval g Runi'')) (⊆-refl Ε)
         (proj₁ (Uni-eval (⊢-weaken (step (same Γ)) f) (Runi' , Suni)) (same Ε) S Suni)
         (proj₁ (Uni-eval f Runi'') (same Ε) S Suni)
         (eval-weaken f (step (same Γ)) (Runi' , Suni) (same Ε) S Suni)) ⟩
      Ε ⊩ υ ∋ _
      ≡⟨ cong (λ G → eval g G (same Ε) (eval f G (same Ε) S)) (⊩ε-purge-refl Γ _) ⟩
      Ε ⊩ υ ∋ _
      ≣⟨ ≣-sym υ (weaken-eval inc g Runi (same Ε) _ (proj₁ Funi (same Ε) S Suni)) ⟩
      Ε ⊩ υ ∋ _
      ≣⟨ proj₁ (proj₂ (Uni-eval g Runi)) _ (proj₁ Funi (same Ε) S Suni)
         (proj₁ (Uni-eval f Runi) _ S Suni) (≣-sym τ (weaken-eval inc f Runi (same Ε) S Suni)) ⟩
      Ε ⊩ υ ∋ eval g R (⊆-trans inc (same Ε)) (eval f R (⊆-trans inc (same Ε)) S)
      ≡⟨ cong (λ pr → eval g R pr (eval f R pr S)) (⊆-same-r inc) ⟩ 
      Ε ⊩ υ ∋ eval g R inc (eval f R inc S)
    Qed

mutual

  abstract

    Unilist-≣ : ∀ {n Γ} (σ : ty n) {S T : Γ ⊩ `list σ} (eq : [ `list σ ] S ≣ T)
      (Suni : Uni[ `list σ ] S) → Uni[ `list σ ] T
    Unilist-≣ σ `[] XSuni = XSuni
    Unilist-≣ σ (hd `∷ tl) (HDuni , TLuni) = Uni-≣ σ hd HDuni , Unilist-≣ σ tl TLuni
    Unilist-≣ σ (mappend {τ} {F₁} {F₂} F xs YS) ((Funi₁ , Funi₂) , YSuni) =
      ((λ inc t → Uni-≣ σ (F inc t) (Funi₁ inc t)) ,
      (λ {Δ} {Ε} i₁ i₂ t →
      Begin[ Ε ⊩ σ ]
        Ε ⊩ σ ∋ ⊩-weaken σ i₁ (F₂ i₂ t)
        ≣⟨ ≣-weaken σ i₁ (≣-sym σ (F i₂ t)) ⟩
        Ε ⊩ σ ∋ ⊩-weaken σ i₁ (F₁ i₂ t)
        ≣⟨ Funi₂ i₁ i₂ t ⟩
        Ε ⊩ σ ∋ F₁ (⊆-trans i₂ i₁) (ne-weaken i₁ t)
        ≣⟨ F (⊆-trans i₂ i₁) (ne-weaken i₁ t) ⟩
        Ε ⊩ σ ∋ F₂ (⊆-trans i₂ i₁) (ne-weaken i₁ t)
      Qed)) ,
      Unilist-≣ σ YS YSuni

    Uni-≣ : ∀ {n Γ} (σ : ty n) {S T : Γ ⊩ σ} (eq : [ σ ] S ≣ T) (Suni : Uni[ σ ] S) → Uni[ σ ] T
    Uni-≣ `1 eq Suni = Suni
    Uni-≣ (`b k) refl Suni = Suni
    Uni-≣ (σ `× τ) (Aeq , Beq) (Auni , Buni) = Uni-≣ σ Aeq Auni , Uni-≣ τ Beq Buni
    Uni-≣ {Γ = Γ} (σ `→ τ) {F} {G} eq (h₁ , h₂ , h₃) =
      (λ inc S Suni → Uni-≣ τ (eq inc S Suni) (h₁ inc S Suni)) ,
      (λ {Δ} inc {S₁} {S₂} Suni₁ Suni₂ eqS₁S₂ →
      Begin[ Δ ⊩ τ ]
        Δ ⊩ τ ∋ G inc S₁
        ≣⟨ ≣-sym τ (eq inc S₁ Suni₁) ⟩
        Δ ⊩ τ ∋ F inc S₁
        ≣⟨ h₂ inc Suni₁ Suni₂ eqS₁S₂ ⟩
        Δ ⊩ τ ∋ F inc S₂
        ≣⟨ eq inc S₂ Suni₂ ⟩
        Δ ⊩ τ ∋ G inc S₂
      Qed) ,
      (λ {Δ} {Ε} i₁ i₂ S Suni →
      Begin[ Ε ⊩ τ ]
        Ε ⊩ τ ∋ ⊩-weaken τ i₁ (G i₂ S)
        ≣⟨ ≣-weaken τ i₁ (≣-sym τ (eq i₂ S Suni)) ⟩
        Ε ⊩ τ ∋ ⊩-weaken τ i₁ (F i₂ S)
        ≣⟨ h₃ i₁ i₂ S Suni ⟩
        Ε ⊩ τ ∋ F (⊆-trans i₂ i₁) (⊩-weaken σ i₁ S)
        ≣⟨ eq (⊆-trans i₂ i₁) (⊩-weaken σ i₁ S) (Uni-weaken σ i₁ Suni) ⟩
        Ε ⊩ τ ∋ G (⊆-trans i₂ i₁) (⊩-weaken σ i₁ S)
      Qed)
    Uni-≣ (`list σ) eq XSuni = Unilist-≣ σ eq XSuni

abstract

  vmap-id : ∀ {n Γ} (σ : ty n) (XS : Γ ⊩ `list σ) → [ `list σ ] XS ≣ vmap σ σ (λ inc S → S) XS
  vmap-id σ `[] = ≣-refl (`list σ) `[]
  vmap-id σ (HD `∷ TL) = ≣-refl σ HD `∷ vmap-id σ TL
  vmap-id σ (mappend F xs YS) = mappend (λ inc t → ≣-refl σ (F inc t)) refl (vmap-id σ YS)

  vmap-comp : ∀ {n Γ} (σ τ υ : ty n) (G : Γ ⊩ τ `→ υ) (F : Γ ⊩ σ `→ τ) (XS : Γ ⊩ `list σ) →
    [ `list υ ] vmap τ υ G (vmap σ τ F XS) ≣ vmap σ υ (λ inc t → G inc (F inc t)) XS
  vmap-comp σ τ υ G F `[] = ≣-refl (`list υ) `[]
  vmap-comp σ τ υ G F (HD `∷ TL) = ≣-refl υ _ `∷ vmap-comp σ τ υ G F TL
  vmap-comp σ τ υ G F (mappend H xs YS) =
    mappend (λ inc t → ≣-refl υ _) refl (vmap-comp σ τ υ G F YS)

  vmap-append : ∀ {n Γ} (σ τ : ty n) (F : Γ ⊩ σ `→ τ) (XS YS : Γ ⊩ `list σ) →
    [ `list τ ] vmap σ τ F (vappend σ XS YS) ≣ vappend τ (vmap σ τ F XS) (vmap σ τ F YS)
  vmap-append σ τ F `[] YS = ≣-refl (`list τ) _
  vmap-append σ τ F (HD `∷ TL) YS = ≣-refl τ _ `∷ vmap-append σ τ F TL YS
  vmap-append σ τ F (mappend G xs TL) YS =
    mappend (λ inc t → ≣-refl τ _) refl (vmap-append σ τ F TL YS)

  vappend-nil : ∀ {n Γ} (σ : ty n) (XS : Γ ⊩ `list σ) → [ `list σ ] XS ≣ vappend σ XS `[]
  vappend-nil σ `[] = ≣-refl (`list σ) `[]
  vappend-nil σ (HD `∷ TL) = ≣-refl σ HD `∷ vappend-nil σ TL
  vappend-nil σ (mappend F xs YS) = mappend (λ inc t → ≣-refl σ (F inc t)) refl (vappend-nil σ YS)

  vappend-assoc : ∀ {n Γ} (σ : ty n) (XS YS ZS : Γ ⊩ `list σ) →
    [ `list σ ] vappend σ (vappend σ XS YS) ZS ≣ vappend σ XS (vappend σ YS ZS)
  vappend-assoc σ `[] YS ZS = ≣-refl (`list σ) (vappend σ YS ZS)
  vappend-assoc σ (HD `∷ TL) YS ZS = ≣-refl σ HD `∷ vappend-assoc σ TL YS ZS
  vappend-assoc σ (mappend F xs TL) YS ZS =
    mappend (λ inc t → ≣-refl σ (F inc t)) refl (vappend-assoc σ TL YS ZS)

  vfold-map : ∀ {n Γ} (σ τ υ : ty n) {C : Γ ⊩ τ `→ υ `→ υ} (Cuni : Uni[ τ `→ υ `→ υ ] C) 
    {N : Γ ⊩ υ} (Nuni : Uni[ υ ] N) {F : Γ ⊩ σ `→ τ} (Funi : Uni[ σ `→ τ ] F)
    (XS : Γ ⊩ `list σ) (XSuni : Uni[ `list σ ] XS) →
    [ υ ] vfold τ υ C N (vmap σ τ F XS) ≣ vfold σ υ (λ inc hd → C inc (F inc hd)) N XS
  vfold-map σ τ υ Cuni Nuni Funi `[] XSuni = ≣-refl υ _
  vfold-map σ τ υ (h₁ , h₂ , h₃) Nuni Funi (HD `∷ TL) (HDuni , TLuni) =
    proj₁ (proj₂ (h₁ (same _) _ (proj₁ Funi (same _) HD HDuni))) (same _)
    (Uni-vfold τ υ (h₁ , h₂ , h₃) Nuni (vmap σ τ _ TL) (Uni-vmap σ Funi TL TLuni))
    (Uni-vfold σ υ (Uni-comp σ τ (υ `→ υ) (h₁ , h₂ , h₃) Funi) Nuni TL TLuni)
    (vfold-map σ τ υ (h₁ , h₂ , h₃) Nuni Funi TL TLuni)
  vfold-map {Γ = Γ} σ τ υ {C} Cuni {N} Nuni {F} Funi (mappend G xs YS) (Guni , YSuni) =
    Begin[ Γ ⊩ υ ]
      Γ ⊩ υ ∋ _
      ≡⟨ cong (λ n → ↓[ υ ] `fold (`λ (`λ (↑[ υ ] C (step (step (same Γ)))
         (F (step (step (same Γ))) (G (step (step (same Γ))) (`v (there here!))))
         (same _) (↓[ υ ] `v here!)))) n xs)
        (≣≡nf υ (vfold-map σ τ υ Cuni Nuni Funi YS YSuni)) ⟩
      Γ ⊩ υ ∋ _
    Qed

  vfold-append : ∀ {n Γ} (σ τ : ty n) {C : Γ ⊩ σ `→ τ `→ τ} (Cuni : Uni[ σ `→ τ `→ τ ] C)
    {N : Γ ⊩ τ} (Nuni : Uni[ τ ] N) (XS : Γ ⊩ `list σ) (XSuni : Uni[ `list σ ] XS)
    {YS : Γ ⊩ `list σ} (YSuni : Uni[ `list σ ] YS) →
    [ τ ] vfold σ τ C N (vappend σ XS YS) ≣ vfold σ τ C (vfold σ τ C N YS) XS
  vfold-append σ τ Cuni Nuni `[] XSuni YSuni = ≣-refl τ _
  vfold-append σ τ (h₁ , h₂ , h₃) Nuni (HD `∷ TL) (HDuni , TLuni) {YS} YSuni =
    proj₁ (proj₂ (h₁ (same _) HD HDuni)) (same _)
    (Uni-vfold σ τ (h₁ , h₂ , h₃) Nuni (vappend σ TL _) (Uni-vappend σ TL TLuni YSuni))
    (Uni-vfold σ τ (h₁ , h₂ , h₃) (Uni-vfold σ τ (h₁ , h₂ , h₃) Nuni YS YSuni) TL TLuni)
    (vfold-append σ τ (h₁ , h₂ , h₃) Nuni TL TLuni YSuni)
  vfold-append {Γ = Γ} σ τ {C} Cuni {N} Nuni (mappend F xs TL) (Funi , TLuni) {YS} YSuni =
    Begin[ Γ ⊩ τ ]
      Γ ⊩ τ ∋ _
      ≡⟨ cong (λ fld → ↓[ τ ] `fold (`λ (`λ (↑[ τ ] C (step (step (same Γ)))
         (F (step (step (same Γ))) (`v (there here!))) (same _) (↓[ τ ] `v here!)))) fld xs)
         (≣≡nf τ (vfold-append σ τ Cuni Nuni TL TLuni YSuni)) ⟩
      Γ ⊩ τ ∋ _
    Qed

abstract

  eval-get : ∀ {n Γ} {σ : ty n} (pr : σ ∈ Γ) {Δ Ε} (γ : Δ ⊢ε Γ) (R : Ε ⊩ε Δ) →
    [ σ ] eval (get pr γ) R ≣ lookup Γ pr (εeval Γ γ R)
  eval-get {σ = σ} here! (_ , g) R = ≣-refl σ (eval g R)
  eval-get (there pr) (γ , _) R = eval-get pr γ R

  eval-subst : ∀ {n Γ} {σ : ty n} (t : Γ ⊢ σ) {Δ Ε} (γ : Δ ⊢ε Γ) {R : Ε ⊩ε Δ} (Runi : Uni[ Δ ]ε R) →
    [ σ ] eval (subst t γ) R ≣ eval t (εeval Γ γ R)
  eval-subst (`v pr) γ Runi = eval-get pr γ _
  eval-subst {Γ = Γ} {σ `→ τ} (`λ t) {Δ} γ {R} Runi =
    λ {Φ} inc S Suni →
    let Runi' = Uniε-weaken Δ inc Runi in
    Begin[ Φ ⊩ τ ]
      Φ ⊩ τ ∋ _
      ≣⟨ eval-subst t _ (Runi' , Suni) ⟩
      Φ ⊩ τ ∋ _
      ≣⟨ ≣-eval t (Uniε-eval Γ _ (Runi' , Suni) , Suni)
         (Uniε-weaken Γ inc (Uniε-eval Γ γ Runi) , Suni)
         ((Begin[ Φ ⊩ε Γ ]
             Φ ⊩ε Γ ∋ _
             ≣⟨ εeval-weaken Γ (step (same Δ)) (Runi' , Suni) ⟩
             Φ ⊩ε Γ ∋ εeval Γ γ (⊩ε-purge (same Δ) (⊩ε-weaken Δ inc R))
             ≡⟨ cong (εeval Γ γ) (⊩ε-purge-refl Δ _) ⟩
             Φ ⊩ε Γ ∋ εeval Γ γ (⊩ε-weaken Δ inc R)
             ≣⟨ ≣ε-sym Γ (weaken-εeval Γ inc γ Runi) ⟩
             Φ ⊩ε Γ ∋ ⊩ε-weaken Γ inc (εeval Γ γ R)
          Qed)
          , ≣-refl σ S) ⟩
      Φ ⊩ τ ∋ _
    Qed
  eval-subst {_} {Γ} {σ} (t `$ u) {Δ} {Ε} γ {R} Runi with Uni-eval (subst t γ) Runi
  ... | h₁ , h₂ , h₃ =
    let Uuni = Uni-eval u (Uniε-eval Γ γ Runi) in
    Begin[ Ε ⊩ σ ]
      Ε ⊩ σ ∋ eval (subst t γ) R (same Ε) (eval (subst u γ) R)
      ≣⟨ h₂ (same Ε) (Uni-eval (subst u γ) Runi) Uuni (eval-subst u γ Runi) ⟩
      Ε ⊩ σ ∋ eval (subst t γ) R (same Ε) (eval u (εeval Γ γ R))
      ≣⟨ eval-subst t γ Runi (same Ε) _ Uuni ⟩
      Ε ⊩ σ ∋ eval t (εeval Γ γ R) (same Ε) (eval u (εeval Γ γ R))
    Qed
  eval-subst `⟨⟩ γ Runi = tt
  eval-subst (a `, b) γ Runi = eval-subst a γ Runi , eval-subst b γ Runi
  eval-subst (`π₁ p) γ Runi = proj₁ (eval-subst p γ Runi)
  eval-subst (`π₂ p) γ Runi = proj₂ (eval-subst p γ Runi)
  eval-subst `[] γ Runi = `[]
  eval-subst (hd `∷ tl) γ Runi = eval-subst hd γ Runi `∷ eval-subst tl γ Runi
  eval-subst {σ = `list σ} (xs `++ ys) γ Runi =
    ≣-vappend σ (eval-subst xs γ Runi) (eval-subst ys γ Runi)
  eval-subst {Γ = Γ} (`map {σ} {τ} f xs) γ Runi =
    ≣-vmap σ τ (Uni-eval (subst f γ) Runi) (eval-subst f γ Runi)
    (Uni-eval (subst xs γ) Runi) (Uni-eval xs (Uniε-eval Γ γ Runi)) (eval-subst xs γ Runi)
  eval-subst {Γ = Γ} (`fold {σ} {τ} c n xs) γ {R} Runi =
    let Guni = Uniε-eval Γ γ Runi in
    ≣-vfold σ τ (Uni-eval (subst c γ) Runi) (Uni-eval c Guni) (eval-subst c γ Runi)
    (Uni-eval (subst n γ) Runi) (Uni-eval n Guni) (eval-subst n γ Runi)
    (Uni-eval (subst xs γ) Runi) (Uni-eval xs Guni) (eval-subst xs γ Runi)

abstract

  ≣-red : ∀ {n Γ Δ} (σ : ty n) {s t} (r : Γ ⊢ σ ∋ s ↝ t) (R : Δ ⊩ε Γ) (Runi : Uni[ Γ ]ε R) →
    [ σ ] eval s R ≣ eval t R
  ≣-red {Γ = Γ} .(σ `→ τ) (`λ {σ} {τ} r) R Runi =
    λ inc S Suni → ≣-red τ r _ (Uniε-weaken Γ inc Runi , Suni)
  ≣-red .τ (`$₁ {σ} {τ} {f} {g} {x} r) R Runi =
    ≣-red (σ `→ τ) r R Runi (same _) (eval x R) (Uni-eval x Runi)
  ≣-red .τ (`$₂ {σ} {τ} {f} {x} {y} r) R Runi with Uni-eval f Runi
  ... | h₁ , h₂ , h₃ = h₂ (same _) (Uni-eval x Runi) (Uni-eval y Runi) (≣-red σ r R Runi)
  ≣-red .(σ `× τ) (`,₁ {σ} {τ} {a} {c} {b} r) R Runi = ≣-red σ r R Runi , ≣-refl τ (eval b R)
  ≣-red .(σ `× τ) (`,₂ {σ} {τ} {a} {b} {d} r) R Runi = ≣-refl σ (eval a R) , ≣-red τ r R Runi
  ≣-red σ (`π₁ r) R Runi = proj₁ (≣-red (σ `× _) r R Runi)
  ≣-red τ (`π₂ r) R Runi = proj₂ (≣-red (_ `× τ) r R Runi)
  ≣-red .(`list σ) (`∷₁ {σ} r) R Runi = ≣-red σ r R Runi `∷ ≣-refl (`list σ) _
  ≣-red .(`list σ) (`∷₂ {σ} r) R Runi = ≣-refl σ _ `∷ ≣-red (`list σ) r R Runi
  ≣-red .(`list σ) (`++₁ {σ} r) R Runi =
    ≣-vappend σ (≣-red (`list σ) r R Runi) (≣-refl (`list σ) _)
  ≣-red .(`list σ) (`++₂ {σ} {xs₁} r) R Runi =
    ≣-vappend σ {XS₁ = eval xs₁ R} (≣-refl (`list σ) _) (≣-red (`list σ) r R Runi)
  ≣-red .(`list τ) (`map₁ {σ} {τ} {f} {g} {xs} r) R Runi =
    let XSuni = Uni-eval xs Runi in
    ≣-vmap σ τ (Uni-eval f Runi) (≣-red (σ `→ τ) r R Runi) XSuni XSuni (≣-refl (`list σ) _)
  ≣-red .(`list τ) (`map₂ {σ} {τ} {f} {xs} {ys} r) R Runi =
    ≣-vmap σ τ (Uni-eval f Runi) (≣-refl (σ `→ τ) (eval f R))
    (Uni-eval xs Runi) (Uni-eval ys Runi) (≣-red (`list σ) r R Runi)
  ≣-red .τ (`fold₁ {σ} {τ} {c₁} {c₂} {n} {xs} r) R Runi =
    let Nuni = Uni-eval n Runi
        XSuni = Uni-eval xs Runi in
    ≣-vfold σ τ (Uni-eval c₁ Runi) (Uni-eval c₂ Runi) (≣-red (σ `→ τ `→ τ) r R Runi)
    Nuni Nuni (≣-refl τ (eval n R)) XSuni XSuni (≣-refl (`list σ) (eval xs R))
  ≣-red .τ (`fold₂ {σ} {τ} {c} {n₁} {n₂} {xs} r) R Runi =
    let Cuni = Uni-eval c Runi
        XSuni = Uni-eval xs Runi in
    ≣-vfold σ τ Cuni Cuni (≣-refl (σ `→ τ `→ τ) (eval c R)) (Uni-eval n₁ Runi) (Uni-eval n₂ Runi)
    (≣-red τ r R Runi) XSuni XSuni (≣-refl (`list σ) (eval xs R))
  ≣-red .τ (`fold₃ {σ} {τ} {c} {n} {xs₁} {xs₂} r) R Runi =
    let Cuni = Uni-eval c Runi
        Nuni = Uni-eval n Runi in
    ≣-vfold σ τ Cuni Cuni (≣-refl (σ `→ τ `→ τ) (eval c R)) Nuni Nuni (≣-refl τ (eval n R))
    (Uni-eval xs₁ Runi) (Uni-eval xs₂ Runi) (≣-red (`list σ) r R Runi)
  ≣-red {_} {Γ} {Δ} .τ (`βλ {σ} {τ} {f} {x}) R Runi =
    let Xuni = Uni-eval x Runi in
    Begin[ Δ ⊩ τ ]
      Δ ⊩ τ ∋ eval f (⊩ε-weaken Γ (same Δ) R , eval x R)
      ≣⟨ ≣-eval f (Uniε-weaken Γ (same Δ) Runi , Xuni) (Uniε-eval Γ (⊢ε-refl Γ) Runi , Xuni)
         ((Begin[ Δ ⊩ε Γ ]
             Δ ⊩ε Γ ∋ ⊩ε-weaken Γ (same Δ) R
             ≣⟨ ≣ε-sym Γ (≣ε-weaken-refl Γ R) ⟩
             Δ ⊩ε Γ ∋ R 
             ≣⟨ ≣ε-sym Γ (εeval-⊢ε-refl Γ Runi) ⟩
             Δ ⊩ε Γ ∋ εeval Γ (⊢ε-refl Γ) R
           Qed)
         , ≣-refl σ (eval x R)) ⟩
      Δ ⊩ τ ∋ eval f (εeval (Γ ∙ σ) (⊢ε-refl Γ , x) R)
      ≣⟨ ≣-sym τ (eval-subst f (⊢ε-refl Γ , x) Runi) ⟩
      Δ ⊩ τ ∋ eval (subst f (⊢ε-refl Γ , x)) R
    Qed
  ≣-red .σ (`βπ₁ {σ} {τ} {a}) R Runi = ≣-refl σ (eval a R)
  ≣-red .τ (`βπ₂ {σ} {τ} {a} {b}) R Runi = ≣-refl τ (eval b R)
  ≣-red .(`list σ) (`β++₁ {σ} {xs}) R Runi = ≣-refl (`list σ) (eval xs R)
  ≣-red .(`list σ) (`β++₂ {σ} {hd} {tl}) R Runi = ≣-refl (`list σ) _
  ≣-red .(`list τ) (`βmap₁ {σ} {τ}) R Runi = ≣-refl (`list τ) `[]
  ≣-red .(`list τ) (`βmap₂ {σ} {τ}) R Runi = ≣-refl (`list τ) _
  ≣-red σ `βfold₁ R Runi = ≣-refl σ _
  ≣-red σ `βfold₂ R Runi = ≣-refl σ _
  ≣-red {_} {Γ} {Δ} .(σ `→ τ) (`ηλ {σ} {τ} f) R Runi =
    λ {Ε} inc S Suni →
    let Runi' = Uniε-weaken Γ inc Runi in
    Begin[ Ε ⊩ τ ]
      Ε ⊩ τ ∋ eval f R inc S
      ≡⟨ cong (λ pr → eval f R pr S) (sym (⊆-same-r inc)) ⟩
      Ε ⊩ τ ∋ eval f R (⊆-trans inc (⊆-refl Ε)) S
      ≣⟨ weaken-eval inc f Runi (same Ε) S Suni ⟩
      Ε ⊩ τ ∋ eval f (⊩ε-weaken Γ inc R) (⊆-refl Ε) S
      ≣⟨ ≣-eval f Runi' (Uniε-purge (same Γ) Runi')
         (≡-to-≣ε Γ (sym (⊩ε-purge-refl Γ (⊩ε-weaken Γ inc R)))) (same Ε) S Suni ⟩
      Ε ⊩ τ ∋ eval f (⊩ε-purge (same Γ) (⊩ε-weaken Γ inc R)) (same Ε) S
      ≣⟨ ≣-sym τ (eval-weaken f (step (same Γ)) (Runi' , Suni) (same Ε) S Suni) ⟩
      Ε ⊩ τ ∋ eval (⊢-weaken (step (⊆-refl Γ)) f) (⊩ε-weaken Γ inc R , S) (same Ε) S
    Qed
  ≣-red .(σ `× τ) {s} (`η× {σ} {τ} .s) R Runi = ≣-refl (σ `× τ) _
  ≣-red .`1 {s} (`η1 .s) R Runi = tt
  ≣-red .(`list σ) (`ηmap₁ {σ} xs) R Runi = vmap-id σ (eval xs R)
  ≣-red .(`list τ) (`ηmap₂ {σ} {τ} {f} xs ys) R Runi =
    vmap-append σ τ (eval f R) (eval xs R) (eval ys R)
  ≣-red {_} {Γ} {Δ} .(`list υ) (`ηmap₃ {σ} {τ} {υ} g f xs) R Runi
    with Uni-eval g Runi | Uni-eval f Runi
  ... | g₁ , g₂ , g₃ | f₁ , f₂ , f₃ =
    let XSuni = Uni-eval xs Runi in
    Begin[ Δ ⊩ `list υ ]
      Δ ⊩ `list υ ∋ _
      ≣⟨ vmap-comp σ τ υ (eval g R) (eval f R) (eval xs R) ⟩
      Δ ⊩ `list υ ∋ _
      ≣⟨ ≣-vmap σ υ (Uni-comp σ τ υ (Uni-eval g Runi) (Uni-eval f Runi))
         (λ {Ε} inc S Suni →
         let RSuni = (Uniε-weaken Γ inc Runi , Suni)
             Funi' = Uni-eval (⊢-weaken (step (same Γ)) f) RSuni in
         Begin[ Ε ⊩ υ ]
           Ε ⊩ υ ∋ eval g R inc (eval f R inc S)
           ≣⟨ g₂ inc (f₁ inc S Suni) (proj₁ Funi' (same Ε) S Suni)
              (Begin[ Ε ⊩ τ ]
                 Ε ⊩ τ ∋ eval f R inc S
                 ≡⟨ cong (λ pr → eval f R pr S) (sym (⊆-same-r inc)) ⟩
                 Ε ⊩ τ ∋ _
                 ≣⟨ weaken-eval inc f Runi (same Ε) S Suni ⟩
                 Ε ⊩ τ ∋ _
                 ≡⟨ cong (λ G → eval f G (same Ε) S) (sym (⊩ε-purge-refl Γ (⊩ε-weaken Γ inc R))) ⟩
                 Ε ⊩ τ ∋ _
                 ≣⟨ ≣-sym τ (eval-weaken f (step (⊆-refl Γ)) RSuni (same Ε) S Suni) ⟩
                 Ε ⊩ τ ∋ eval (⊢-weaken (step (same Γ)) f) (⊩ε-weaken Γ inc R , S) (same Ε) S
               Qed) ⟩
           Ε ⊩ υ ∋ _
           ≡⟨ cong (λ pr → eval g R pr (eval (⊢-weaken (step {σ = σ} (same Γ)) f)
              (⊩ε-weaken Γ inc R , S) (same Ε) S)) (sym (⊆-same-r inc)) ⟩
           Ε ⊩ υ ∋ _
           ≣⟨ weaken-eval inc g Runi (same Ε) _ (proj₁ Funi' (same Ε) S Suni) ⟩
           Ε ⊩ υ ∋ _
           ≡⟨ cong (λ G → eval g G (same Ε) (eval (⊢-weaken (step {σ = σ} (same Γ)) f)
              (⊩ε-weaken Γ inc R , S) (same Ε) S)) (sym (⊩ε-purge-refl Γ (⊩ε-weaken Γ inc R))) ⟩
           Ε ⊩ υ ∋ _
           ≣⟨ ≣-sym υ (eval-weaken g (step (⊆-refl Γ)) RSuni
              (same Ε) _ (proj₁ Funi' (same Ε) S Suni)) ⟩
           Ε ⊩ υ ∋ _
         Qed)
         XSuni XSuni (≣-refl (`list σ) (eval xs R)) ⟩
      Δ ⊩ `list υ ∋ _
    Qed
  ≣-red .τ (`ηfold₁ {σ} {τ} {c} {n} xs ys) R Runi =
    vfold-append σ τ (Uni-eval c Runi) (Uni-eval n Runi) (eval xs R)
    (Uni-eval xs Runi) (Uni-eval ys Runi)
  ≣-red {_} {Γ} {Δ} .υ (`ηfold₂ {τ} {υ} {σ} {n} c f xs) R Runi =
    let Cuni = Uni-eval c Runi
        Nuni = Uni-eval n Runi
        Funi = Uni-eval f Runi
        XSuni = Uni-eval xs Runi
        CFuni = Uni-comp σ τ (υ `→ υ) Cuni Funi
        EQ : [ σ `→ υ `→ υ ] (λ inc t → eval c R inc (eval f R inc t)) ≣ eval (c `∘ f) R
        EQ = ≣-sym (σ `→ υ `→ υ) (eval-comp σ τ (υ `→ υ) f c Runi)
    in
    Begin[ Δ ⊩ υ ]
      Δ ⊩ υ ∋ eval (`fold c n (`map f xs)) R
      ≣⟨ vfold-map σ τ υ Cuni Nuni Funi (eval xs R) XSuni ⟩
      Δ ⊩ υ ∋ _
-- you tricky bastard! Why proving complicated stuff
-- when we can use an equality that we ALREADY have to prove?! :]
      ≣⟨ ≣-vfold σ υ CFuni (Uni-≣ (σ `→ υ `→ υ) EQ CFuni) EQ
         Nuni Nuni (≣-refl υ (eval n R)) XSuni XSuni (≣-refl (`list σ) (eval xs R)) ⟩
      Δ ⊩ υ ∋ _
    Qed
  ≣-red .(`list σ) (`η++₁ {σ} xs) R Runi = vappend-nil σ (eval xs R)
  ≣-red .(`list σ) (`η++₂ {σ} xs ys zs) R Runi = vappend-assoc σ (eval xs R) (eval ys R) (eval zs R)


abstract

  ≣-reds : ∀ {n Γ} (σ : ty n) {s t} (r : Γ ⊢ σ ∋ s ≅ t) {Δ} {R : Δ ⊩ε Γ} (Runi : Uni[ Γ ]ε R) →
    [ σ ] eval s R ≣ eval t R
  ≣-reds σ refl Runi = ≣-refl σ _
  ≣-reds σ (lstep p r) Runi = ≣-trans σ (≣-red σ p _ Runi) (≣-reds σ r Runi)
  ≣-reds σ (rstep p r) Runi = ≣-trans σ (≣-sym σ (≣-red σ p _ Runi)) (≣-reds σ r Runi)

  completeness : ∀ {n} {σ : ty n} {Γ s t} (r : Γ ⊢ σ ∋ s ≅ t) → norm s ≡ norm t
  completeness {_} {σ} {Γ} req = cong back-nf (≣≡nf σ (≣-reds σ req (Uni-⊩ε-refl Γ)))