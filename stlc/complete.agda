module stlc.complete where

open import Data.Unit
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality renaming (subst to coerce ; subst₂ to coerce₂)

open import tools.contexts
open import tools.closures
open import stlc.definition
open import stlc.reductions
open import stlc.model
open import stlc.eval

{- definition of semantical equality (extensional) and uniformity -}

infix 3 [_]_≣_ [_]_≣ε_

mutual

  [_]_≣_ : ∀ {Γ} σ {s t} (S : Γ ⊩τ σ [ s ]) (T : Γ ⊩τ σ [ t ]) → Set
  [ ♭ ] (a , ra) ≣ (b , rb) = a ≡ b
  [ σ ▹ τ ] F ≣ G =
    ∀ {Δ} inc {s : Δ ⊢ σ} (S : Δ ⊩τ σ [ s ]) (Suni : Uni[ Δ , σ ] S) →
    [ τ ] F inc S ≣ G inc S

  Uni[_,_]_ : ∀ Γ σ {s} (S : Γ ⊩τ σ [ s ]) → Set
  Uni[ Γ , ♭ ] S = ⊤
  Uni[ Γ , σ ▹ τ ] F =
    (∀ {Δ} (inc : Γ ⊆ Δ) {s} (S : Δ ⊩τ σ [ s ]) (Suni : Uni[ Δ , σ ] S) → Uni[ Δ , τ ] F inc S) ×
    (∀ {Δ} (inc : Γ ⊆ Δ) {s₁} (S₁ : Δ ⊩τ σ [ s₁ ]) {s₂} (S₂ : Δ ⊩τ σ [ s₂ ])
      (Suni₁ : Uni[ Δ , σ ] S₁) (Suni₂ : Uni[ Δ , σ ] S₂) (eq : [ σ ] S₁ ≣ S₂) →
      [ τ ] F inc S₁ ≣ F inc S₂) ×
    (∀ {Δ} {Ε} (i₁ : Δ ⊆ Ε) (i₂ : Γ ⊆ Δ) {s} (S : Δ ⊩τ σ [ s ]) (Suni : Uni[ Δ , σ ] S) →
      [ τ ] ⊩τ-weaken _ i₁ (F i₂ S) ≣ F (⊆-trans i₂ i₁) (⊩τ-weaken s i₁ S))

[_]_≣ε_ : ∀ {Δ} Γ {γ ρ} (G : Δ ⊩ε Γ [ γ ]) (R : Δ ⊩ε Γ [ ρ ]) → Set
[ ε ] G ≣ε R = ⊤
[ Γ ∙ σ ] g , G ≣ε r , R = [ Γ ] G ≣ε R × [ σ ] g ≣ r

Uni[_,ε_]_ : ∀ Δ Γ {γ} (G : Δ ⊩ε Γ [ γ ]) → Set
Uni[ Δ ,ε ε ] G = ⊤
Uni[ Δ ,ε Γ ∙ σ ] (g , G) = Uni[ Δ ,ε Γ ] G × Uni[ Δ , σ ] g

εpurge : ∀ {Γ Δ} (inc : Γ ⊆ Δ) {Ε ρ} (R : Ε ⊩ε Δ [ ρ ]) → Ε ⊩ε Γ [ purge inc ρ ]
εpurge base R = R
εpurge (step inc) (_ , R) = εpurge inc R
εpurge (pop! inc) (r , R) = r , εpurge inc R

{- _≣_ is an equivalence relation and so is _≣ε_ -}

abstract

  ≣-refl : ∀ σ {Γ} {s} (S : Γ ⊩τ σ [ s ]) → [ σ ] S ≣ S
  ≣-refl ♭ S = refl
  ≣-refl (σ ▹ τ) F = λ inc S Suni → ≣-refl τ (F inc S)

  ≣ε-refl : ∀ Γ {Δ} {ρ} (R : Δ ⊩ε Γ [ ρ ]) → [ Γ ] R ≣ε R
  ≣ε-refl ε R = R
  ≣ε-refl (Γ ∙ σ) (r , R) = ≣ε-refl Γ R , ≣-refl σ r

  ≣-sym : ∀ σ {Γ} {s} {S : Γ ⊩τ σ [ s ]} {t} {T : Γ ⊩τ σ [ t ]} (eq : [ σ ] S ≣ T) → [ σ ] T ≣ S
  ≣-sym ♭ {S = (a , ra)} {T = (.a , rb)} refl = refl
  ≣-sym (σ ▹ τ) eq = λ inc S Suni → ≣-sym τ (eq inc S Suni)

  ≣ε-sym : ∀ Γ {Δ} {γ} {G : Δ ⊩ε Γ [ γ ]} {ρ} {R : Δ ⊩ε Γ [ ρ ]} (eq : [ Γ ] G ≣ε R) → [ Γ ] R ≣ε G
  ≣ε-sym ε eq = eq
  ≣ε-sym (Γ ∙ σ) (eqΓ , eqσ) = ≣ε-sym Γ eqΓ , ≣-sym σ eqσ

  ≣-trans : ∀ σ {Γ} {s} {S : Γ ⊩τ σ [ s ]} {t} {T : Γ ⊩τ σ [ t ]} {u} {U : Γ ⊩τ σ [ u ]}
            (eqST : [ σ ] S ≣ T) (eqTU : [ σ ] T ≣ U) → [ σ ] S ≣ U
  ≣-trans ♭ {S = a , ra} {T = .a  , rb} {U = .a , rc} refl refl = refl
  ≣-trans (σ ▹ τ) eqST eqTU = λ inc S Suni → ≣-trans τ (eqST inc S Suni) (eqTU inc S Suni)

  ≣ε-trans : ∀ Γ {Δ} {γ} {G : Δ ⊩ε Γ [ γ ]} {δ} {D : Δ ⊩ε Γ [ δ ]} {ρ} {R : Δ ⊩ε Γ [ ρ ]}
            (eqGD : [ Γ ] G ≣ε D) (eqDR : [ Γ ] D ≣ε R) → [ Γ ] G ≣ε R
  ≣ε-trans ε eqGD eqDR = tt
  ≣ε-trans (Γ ∙ σ) (eqGD , eqgd) (eqDR , eqdr) = ≣ε-trans Γ eqGD eqDR , ≣-trans σ eqgd eqdr

{- ≣ and Uni are compatible with weakening -}

abstract

  ≣-coerce : ∀ {Γ} σ {τ} (f : Γ ⊢ τ → Γ ⊢ σ) {s} {S : Γ ⊩τ σ [ f s ]}
    {t} (pr : s ≡ t) → [ σ ] S ≣ coerce (λ s → Γ ⊩τ σ [ f s ]) pr S
  ≣-coerce σ f refl = ≣-refl σ _

  ≣-weaken : ∀ {Γ Δ} σ {s t} {S : Γ ⊩τ σ [ s ]} {T : Γ ⊩τ σ [ t ]} (inc : Γ ⊆ Δ)
    (eq : [ σ ] S ≣ T) → [ σ ] ⊩τ-weaken s inc S ≣ ⊩τ-weaken t inc T
  ≣-weaken ♭ {S = a , ra} {T = .a , rb} inc refl = refl
  ≣-weaken (σ ▹ τ) {f} {g} inc eq =
    λ {Ε} inc' {s} S Suni →
    ≣-trans τ (≣-sym τ (≣-coerce τ (λ t → app t s) (sym (weaken² inc inc' f))))
   (≣-trans τ (eq (⊆-trans inc inc') S Suni)
   (≣-coerce τ (λ t → app t s) (sym (weaken² inc inc' g))))

  ≣ε-weaken : ∀ {Δ Ε} Γ {γ ρ} {G : Δ ⊩ε Γ [ γ ]} {R : Δ ⊩ε Γ [ ρ ]} (inc : Δ ⊆ Ε)
    (eq : [ Γ ] G ≣ε R) → [ Γ ] ⊩ε-weaken Γ inc G ≣ε ⊩ε-weaken Γ inc R
  ≣ε-weaken ε inc eq = eq
  ≣ε-weaken (Γ ∙ σ) inc (Eq , eq) = ≣ε-weaken Γ inc Eq , ≣-weaken σ inc eq

  ≣-weaken-refl : ∀ {Γ} σ {s} (S : Γ ⊩τ σ [ s ]) → [ σ ] S ≣ ⊩τ-weaken s (same _) S
  ≣-weaken-refl ♭ S = weaken-ne-refl _
  ≣-weaken-refl (σ ▹ τ) F =
    λ {Δ} inc {s} S Suni →
    ≣-trans τ (coerce (λ pr → [ τ ] F inc S ≣ F pr S) (sym (⊆-same-l inc)) (≣-refl τ (F inc S)))
   (≣-coerce τ (λ f → app f s) (sym (weaken² (⊆-refl _) inc _)))

  ≣ε-weaken-refl : ∀ {Δ} Γ {ρ} (R : Δ ⊩ε Γ [ ρ ]) → [ Γ ] R ≣ε ⊩ε-weaken Γ (same _) R
  ≣ε-weaken-refl ε R = tt
  ≣ε-weaken-refl (Γ ∙ σ) (r , R) = ≣ε-weaken-refl Γ R , ≣-weaken-refl σ r

  ≣-weaken² : ∀ {Γ Δ Ε} σ {s} {S : Γ ⊩τ σ [ s ]} (inc : Γ ⊆ Δ) (inc' : Δ ⊆ Ε) →
    [ σ ] ⊩τ-weaken _ inc' (⊩τ-weaken s inc S) ≣ ⊩τ-weaken s (⊆-trans inc inc') S
  ≣-weaken² ♭ inc inc' = weaken-ne² inc inc' _
  ≣-weaken² (σ ▹ τ) {S = F} inc inc' =
    λ {φ} inc'' {s} S Suni →
    ≣-trans τ (≣-sym τ (≣-coerce τ (λ t → app t s) (sym (weaken² inc' inc'' (weaken inc _)))))
   (≣-trans τ (≣-sym τ (≣-coerce τ (λ t → app t s) (sym (weaken² inc (⊆-trans inc' inc'') _))))
   (≣-trans τ (coerce (λ pr → [ τ ] F pr S ≣ F (⊆-trans (⊆-trans inc inc') inc'') S)
      (sym (⊆-assoc inc inc' inc''))
   (≣-refl τ (F (⊆-trans (⊆-trans inc inc') inc'') S)))
   (≣-coerce τ (λ t → app t s) (sym (weaken² (⊆-trans inc inc') inc'' _)))))

  ≣ε-weaken² : ∀ {Δ Ε Φ} Γ {ρ} {R : Δ ⊩ε Γ [ ρ ]} (inc : Δ ⊆ Ε) (inc' : Ε ⊆ Φ) →
    [ Γ ] ⊩ε-weaken Γ inc' (⊩ε-weaken Γ inc R) ≣ε ⊩ε-weaken Γ (⊆-trans inc inc') R
  ≣ε-weaken² ε inc inc' = tt
  ≣ε-weaken² (Γ ∙ σ) inc inc' = ≣ε-weaken² Γ inc inc' , ≣-weaken² σ inc inc'

  Uni-coerce : ∀ {Γ} σ {τ} (f : Γ ⊢ τ → Γ ⊢ σ) {s} {S : Γ ⊩τ σ [ f s ]}
    {t} (pr : s ≡ t) (SUni : Uni[ Γ , σ ] S) → Uni[ Γ , σ ] coerce (λ s → Γ ⊩τ σ [ f s ]) pr S
  Uni-coerce σ f refl SUni = SUni

  Uni-weaken : ∀ {Γ Δ} σ {s} {S : Γ ⊩τ σ [ s ]} (inc : Γ ⊆ Δ)
    (SUni : Uni[ Γ , σ ] S) → Uni[ Δ , σ ] ⊩τ-weaken s inc S
  Uni-weaken ♭ inc SUni = SUni
  Uni-weaken (σ ▹ τ) {f} {F} inc (h₁ , h₂ , h₃) =
    (λ {Ε} inc' {s} S Suni →
       Uni-coerce τ (λ t → app t s) (sym (weaken² inc inc' _)) (h₁ (⊆-trans inc inc') S Suni)) ,
    (λ {Ε} inc' {s₁} S₁ {s₂} S₂ Suni₁ Suni₂ eqS₁S₂ →
       ≣-trans τ (≣-sym τ (≣-coerce τ (λ t → app t s₁) (sym (weaken² inc inc' _))))
      (≣-trans τ (h₂ (⊆-trans inc inc') S₁ S₂ Suni₁ Suni₂ eqS₁S₂)
      (≣-coerce τ (λ t → app t s₂) (sym (weaken² inc inc' _))))) ,
    (λ i₁ i₂ {s} S Suni →
       ≣-trans τ (≣-weaken τ i₁ (≣-sym τ (≣-coerce τ (λ t → app t s) (sym (weaken² inc i₂ _)))))
      (≣-trans τ (h₃ i₁ (⊆-trans inc i₂) S Suni)
      (≣-trans τ (coerce (λ pr → [ τ ] F pr (⊩τ-weaken s i₁ S) ≣
         F (⊆-trans inc (⊆-trans i₂ i₁)) (⊩τ-weaken s i₁ S)) (⊆-assoc inc i₂ i₁) (≣-refl τ _))
      (≣-coerce τ (λ t → app t (weaken i₁ s)) (sym (weaken² inc (⊆-trans i₂ i₁) _))))))

  Uniε-weaken : ∀ {Δ Ε} Γ {ρ} {R : Δ ⊩ε Γ [ ρ ]} (inc : Δ ⊆ Ε)
    (Runi : Uni[ Δ ,ε Γ ] R) → Uni[ Ε ,ε Γ ] ⊩ε-weaken Γ inc R
  Uniε-weaken ε inc Runi = Runi
  Uniε-weaken (Γ ∙ σ) inc (Runi , runi) = Uniε-weaken Γ inc Runi , Uni-weaken σ inc runi

{- ≣ and Uni are compatible with anti-reductions casts -}

abstract

  ≣-⊩τ-◃ : ∀ σ {Γ} {t} (S : Γ ⊩τ σ [ t ]) {s} (r : Γ ⊢ σ ∋ s ▹ t) → [ σ ] S ≣ ⊩τ-◃ r S
  ≣-⊩τ-◃ ♭ S r = refl
  ≣-⊩τ-◃ (σ ▹ τ) F r = λ inc S Suni → ≣-⊩τ-◃ τ (F inc S) (apl (▹-weaken inc r))

  Uni-⊩τ-◃ : ∀ σ {Γ} {t} (S : Γ ⊩τ σ [ t ]) {s} (r : Γ ⊢ σ ∋ s ▹ t)
    (Suni : Uni[ Γ , σ ] S) → Uni[ Γ , σ ] ⊩τ-◃ r S
  Uni-⊩τ-◃ ♭ S r Suni = Suni
  Uni-⊩τ-◃ (σ ▹ τ) F r (h₁ , h₂ , h₃) =
    (λ inc S Suni → Uni-⊩τ-◃ τ (F inc S) (apl (▹-weaken inc r)) (h₁ inc S Suni)) ,
    (λ inc S₁ S₂ Suni₁ Suni₂ eqS₁S₂ →
      ≣-trans τ (≣-sym τ (≣-⊩τ-◃ τ (F inc S₁) (apl (▹-weaken inc r))))
     (≣-trans τ (h₂ inc S₁ S₂ Suni₁ Suni₂ eqS₁S₂)
     (≣-⊩τ-◃ τ (F inc S₂) (apl (▹-weaken inc r))))) ,
    (λ i₁ i₂ S Suni →
      ≣-trans τ (≣-weaken τ i₁ (≣-sym τ (≣-⊩τ-◃ τ (F i₂ S) (apl (▹-weaken i₂ r)))))
     (≣-trans τ (h₃ i₁ i₂ S Suni)
     (≣-⊩τ-◃ τ (F _ (⊩τ-weaken _ i₁ S)) (apl (▹-weaken _ r)))))

  ≣-⊩τ-⋆◃ : ∀ σ {Γ} {t} (S : Γ ⊩τ σ [ t ]) {s} (r : s ▹⋆ t) → [ σ ] S ≣ ⊩τ-⋆◃ r S
  ≣-⊩τ-⋆◃ σ S refl = ≣-refl σ S
  ≣-⊩τ-⋆◃ σ S (step p r) = ≣-trans σ (≣-⊩τ-⋆◃ σ S r) (≣-⊩τ-◃ σ _ p)

  Uni-⊩τ-⋆◃ : ∀ σ {Γ} {t} (S : Γ ⊩τ σ [ t ]) {s} (r : s ▹⋆ t)
    (Suni : Uni[ Γ , σ ] S) → Uni[ Γ , σ ] ⊩τ-⋆◃ r S
  Uni-⊩τ-⋆◃ σ S refl Suni = Suni
  Uni-⊩τ-⋆◃ σ S (step p r) Suni = Uni-⊩τ-◃ σ _ p (Uni-⊩τ-⋆◃ σ S r Suni)

{- weakening and activation can be swapped -}

  weaken-↓ : ∀ {Γ Δ} σ (inc : Γ ⊆ Δ) (t : Γ ⊢ne σ) →
    [ σ ] ⊩τ-weaken _ inc (↓ t) ≣ ↓ (weaken-ne inc t)
  weaken-↓ ♭ inc t = refl
  weaken-↓ (σ ▹ τ) inc t =
    λ {Ε} inc' {s} S Suni →
    ≣-trans τ (≣-sym τ (≣-coerce τ (λ t → app t s) (sym (weaken² inc inc' (back-ne t)))))
   (≣-trans τ (≣-sym τ (≣-⊩τ-⋆◃ τ (↓ (app (weaken-ne (⊆-trans inc inc') t) (↑ S)))
      (coerce (λ z → reftranclos (_⊢_∋_▹_ Ε τ) (app (weaken (⊆-trans inc inc') (back-ne t)) s)
      (app z (back-nf (↑ S)))) (sym (back-weaken-ne (⊆-trans inc inc') t)) (▹⋆-cong apr (↑▹⋆ σ s S)))))
   (≣-trans τ (coerce (λ t' → [ τ ] ↓ (app (weaken-ne (⊆-trans inc inc') t) (↑ S)) ≣ ↓ (app t' (↑ S)))
     (sym (weaken-ne² inc inc' t)) (≣-refl τ _))
   (≣-⊩τ-⋆◃ τ (↓ (app (weaken-ne inc' (weaken-ne inc t)) (↑ S)))
      (coerce (λ z → reftranclos (_⊢_∋_▹_ Ε τ) (app (weaken inc' (back-ne (weaken-ne inc t))) s)
      (app z (back-nf (↑ S)))) (sym (back-weaken-ne inc' (weaken-ne inc t)))
      (▹⋆-cong apr (↑▹⋆ σ s S))))))

mutual

{- activated neutrals are uniform -}

  abstract

    Uni-ne : ∀ σ {Γ} (t : Γ ⊢ne σ) → Uni[ Γ , σ ] ↓ t
    Uni-ne ♭ t = tt
    Uni-ne (σ ▹ τ) t =
      (λ {Δ} inc {s} S Suni → 
        Uni-⊩τ-⋆◃ τ (↓ (app (weaken-ne inc t) (↑ S)))
          (coerce (λ z → reftranclos (_⊢_∋_▹_ _ τ) (app (weaken inc (back-ne t)) s)
          (app z (back-nf (↑ S)))) (sym (back-weaken-ne inc t)) (▹⋆-cong apr (↑▹⋆ σ s S)))
       (Uni-ne τ (app (weaken-ne inc t) (↑ S)))) ,
      (λ {Δ} inc {s₁} S₁ {s₂} S₂ Suni₁ Suni₂ eq →
        ≣-trans τ (≣-sym τ (≣-⊩τ-⋆◃ τ (↓ (app (weaken-ne inc t) (↑ S₁)))
          (coerce (λ z → reftranclos (_⊢_∋_▹_ Δ τ) (app (weaken inc (back-ne t)) s₁)
          (app z (back-nf (↑ S₁)))) (sym (back-weaken-ne inc t)) (▹⋆-cong apr (↑▹⋆ σ s₁ S₁)))))
       (≣-trans τ (coerce (λ s → [ τ ] ↓ (app (weaken-ne inc t) (↑ S₁)) ≣ ↓ (app (weaken-ne inc t) s))
          (≣-≡nf σ eq) (≣-refl τ (↓ (app (weaken-ne inc t) (↑ S₁)))))
       (≣-⊩τ-⋆◃ τ (↓ (app (weaken-ne inc t) (↑ S₂)))
          (coerce (λ z → reftranclos (_⊢_∋_▹_ Δ τ) (app (weaken inc (back-ne t)) s₂)
          (app z (back-nf (↑ S₂)))) (sym (back-weaken-ne inc t)) (▹⋆-cong apr (↑▹⋆ σ s₂ S₂)))))) ,
      (λ {Δ} {Ε} i₁ i₂ {s} S Suni →
        ≣-trans τ (≣-trans τ (≣-weaken τ i₁ (≣-sym τ (≣-⊩τ-⋆◃ τ (↓ (app (weaken-ne i₂ t) (↑ S)))
          (coerce (λ z → reftranclos (_⊢_∋_▹_ Δ τ) (app (weaken i₂ (back-ne t)) s)
          (app z (back-nf (↑ S)))) (sym (back-weaken-ne i₂ t)) (▹⋆-cong apr (↑▹⋆ σ s S))))))
       (≣-trans τ (weaken-↓ τ i₁ (app (weaken-ne i₂ t) (↑ S)))
          (coerce₂ (λ s' t' → [ τ ] ↓ (app t' (weaken-nf i₁ (↑ S))) ≣
          ↓ (app (weaken-ne (⊆-trans i₂ i₁) t) s')) (sym (weaken-↑ σ i₁ S Suni))
          (sym (weaken-ne² i₂ i₁ t)) (≣-refl τ _))))
       (≣-⊩τ-⋆◃ τ (↓ (app (weaken-ne (⊆-trans i₂ i₁) t) (↑ (⊩τ-weaken s i₁ S))))
          (coerce (λ z → reftranclos (_⊢_∋_▹_ Ε τ) (app (weaken (⊆-trans i₂ i₁) (back-ne t))
          (weaken i₁ s)) (app z (back-nf (↑ (⊩τ-weaken s i₁ S))))) (sym (back-weaken-ne _ t))
          (▹⋆-cong apr (↑▹⋆ σ (weaken i₁ s) (⊩τ-weaken s i₁ S))))))

{- Equivalent semantical object are quoted to equal normal forms! -}

  abstract

    ≣-≡nf : ∀ {Γ} σ {s t} {S : Γ ⊩τ σ [ s ]} {T : Γ ⊩τ σ [ t ]} (eq : [ σ ] S ≣ T) → ↑ S ≡ ↑ T
    ≣-≡nf ♭ {S = a , ra} {T = .a  , rb} refl = refl
    ≣-≡nf (σ ▹ τ) eq =
      cong lam (≣-≡nf τ (eq (step (same _)) (↓ (var here!)) (Uni-ne σ (var here!))))

{- Uniform semantical objects can be weakened before or after quoting -}

  abstract

    weaken-↑ : ∀ σ {Γ Δ} (inc : Γ ⊆ Δ) {s} (S : Γ ⊩τ σ [ s ]) (Suni : Uni[ Γ , σ ] S) →
      ↑ (⊩τ-weaken s inc S) ≡ weaken-nf inc (↑ S)
    weaken-↑ ♭ inc S Suni = refl
    weaken-↑ (σ ▹ τ) {Γ} {Δ} inc {s} S (h₁ , h₂ , h₃) =
      cong lam (trans (≣-≡nf τ (≣-trans τ (≣-sym τ
     (≣-coerce τ (λ f → app f (var here!)) (sym (weaken² inc (step (same Δ)) s))))
     (≣-trans τ (≣-trans τ (coerce (λ pr → [ τ ] S (⊆-trans inc (step (same _))) (↓ (var here!)) ≣
        S pr (↓ (var here!))) (sym (⊆-step-same inc)) (≣-refl τ _))
     (h₂ (step (⊆-trans (same Γ) inc)) (↓ (var here!))
        (⊩τ-weaken (back-ne (var here!)) (pop! inc) (↓ (var here!))) (Uni-ne σ (var here!))
        (Uni-weaken σ (pop! inc) (Uni-ne σ (var here!)))
        (≣-sym σ (weaken-↓ σ (pop! inc) (var here!)))))
     (≣-sym τ (h₃ (pop! inc) (step (same Γ)) (↓ (var here!)) (Uni-ne σ (var here!)))))))
      (weaken-↑ τ (pop! inc) (S (step (same _)) (↓ (var here!)))
        (h₁ (step (same _)) (↓ (var here!)) (Uni-ne σ (var here!)))))

Uni-Γ⊩ : ∀ Γ → Uni[ Γ ,ε Γ ] Γ⊩ε Γ
Uni-Γ⊩ ε = tt
Uni-Γ⊩ (Γ ∙ σ) = Uniε-weaken Γ (step (⊆-refl Γ)) (Uni-Γ⊩ Γ) , Uni-ne σ (var here!)

{- Equivalent semantical objects come from related elements -}

abstract

  ≣-back : ∀ {Γ} σ {s t} {S : Γ ⊩τ σ [ s ]} {T : Γ ⊩τ σ [ t ]} (eq : [ σ ] S ≣ T) → s ≡βη t
  ≣-back ♭ {S = s , rs} {T = .s , rt} refl = ≡⋆-trans (▹≡⋆ rs) (≡⋆-sym (▹≡⋆ rt))
  ≣-back (σ ▹ τ) {S = F} {T = G} eq =
    lstep eta (≡⋆-sym (lstep eta 
    (≡⋆-cong lam (≡⋆-sym (≣-back τ (eq (step (same _))(↓ (var here!)) (Uni-ne σ (var here!))))))))

{- evaluation produces uniform terms -}

abstract

  Uni-lookup : ∀ {Γ Δ σ} (pr : σ ∈ Γ) {ρ} {R : Δ ⊩ε Γ [ ρ ]}
    (Runi : Uni[ Δ ,ε Γ ] R) → Uni[ Δ , σ ] (lookup pr R)
  Uni-lookup here! (_ , runi) = runi
  Uni-lookup (there pr) (Runi , _) = Uni-lookup pr Runi

  ≣-lookup : ∀ {Γ Δ σ} (pr : σ ∈ Γ) {ρ₁} {R₁ : Δ ⊩ε Γ [ ρ₁ ]} {ρ₂} {R₂ : Δ ⊩ε Γ [ ρ₂ ]}
    (eqR₁R₂ : [ Γ ] R₁ ≣ε R₂) → [ σ ] lookup pr R₁ ≣ lookup pr R₂
  ≣-lookup here! (_ , eqr₁r₂) = eqr₁r₂
  ≣-lookup (there pr) (eqR₁R₂ , _) = ≣-lookup pr eqR₁R₂

  weaken-lookup : ∀ {Γ Δ Ε σ} (inc : Δ ⊆ Ε) (pr : σ ∈ Γ) {ρ} (R : Δ ⊩ε Γ [ ρ ]) →
    [ σ ] ⊩τ-weaken _ inc (lookup pr R) ≣ lookup pr (⊩ε-weaken Γ inc R)
  weaken-lookup inc here! (r , _) = ≣-refl _ _
  weaken-lookup inc (there pr) (_ , R) = weaken-lookup inc pr R

mutual

  abstract

  {- evaluation in uniform environments yields uniform objects -}

    Uni-eval : ∀ {Γ Δ σ} (t : Γ ⊢ σ) {ρ} {R : Δ ⊩ε Γ [ ρ ]}
      (Runi : Uni[ Δ ,ε Γ ] R) → Uni[ Δ , σ ] (eval t R)
    Uni-eval (var pr) Runi = Uni-lookup pr Runi
    Uni-eval {Γ} {Δ} (lam {σ} {τ} t) {ρ} Runi =
      (λ {Ε} inc {s} S Suni →
        Uni-⊩τ-◃ τ _ (red (weaken (pop! inc) (subst t (var here! , ⊩-weaken Γ (step (same _)) ρ))) s)
          (Uni-coerce τ id (sym (trans (cong (λ t → subst t (s , Γ⊩ Ε))
          (weaken-subst (pop! inc) t (var here! , ⊩-weaken Γ (step (same Δ)) ρ)))
          (trans (cong (λ ρ → β-reduce (subst t (var here! , ρ)) s)
          (trans (⊩-weaken² Γ (step (same Δ)) (pop! inc) ρ)
          (trans (cong (λ pr → ⊩-weaken Γ pr ρ) (⊆-step-same inc))
          (sym (⊩-weaken² Γ inc (step (same Ε)) ρ))))) (βsubst t s (⊩-weaken Γ inc ρ)))))
          (Uni-eval t (Uniε-weaken Γ inc Runi , Suni)))) ,
      (λ {Ε} inc {s₁} S₁ {s₂} S₂ Suni₁ Suni₂ eqS₁S₂ →
        ≣-trans τ (≣-sym τ (≣-trans τ (≣-coerce τ id (sym (trans (cong (λ t → subst t (s₁ , Γ⊩ Ε))
          (weaken-subst (pop! inc) t (var here! , ⊩-weaken Γ (step (same Δ)) ρ)))
          (trans (cong (λ ρ → β-reduce (subst t (var here! , ρ)) s₁)
          (trans (⊩-weaken² Γ (step (same Δ)) (pop! inc) ρ)
          (trans (cong (λ pr → ⊩-weaken Γ pr ρ) (⊆-step-same inc))
          (sym (⊩-weaken² Γ inc (step (same Ε)) ρ))))) (βsubst t s₁ (⊩-weaken Γ inc ρ))))))
       (≣-⊩τ-◃ τ _ (red (weaken (pop! inc) (subst t (var here! , ⊩-weaken Γ (step (same Δ)) ρ))) s₁))))
       (≣-trans τ (≣-eval t (Uniε-weaken Γ inc Runi , Suni₁) (Uniε-weaken Γ inc Runi , Suni₂)
         (≣ε-refl Γ (⊩ε-weaken Γ inc _) , eqS₁S₂))
       (≣-trans τ (≣-coerce τ id (sym (trans (cong (λ t → subst t (s₂ , Γ⊩ Ε))
          (weaken-subst (pop! inc) t (var here! , ⊩-weaken Γ (step (same Δ)) ρ)))
          (trans (cong (λ ρ → β-reduce (subst t (var here! , ρ)) s₂)
          (trans (⊩-weaken² Γ (step (same Δ)) (pop! inc) ρ)
          (trans (cong (λ pr → ⊩-weaken Γ pr ρ) (⊆-step-same inc))
          (sym (⊩-weaken² Γ inc (step (same Ε)) ρ))))) (βsubst t s₂ (⊩-weaken Γ inc ρ))))))
       (≣-⊩τ-◃ τ _ (red (weaken (pop! inc) (subst t (var here! ,
          ⊩-weaken Γ (step (same Δ)) ρ))) s₂))))) ,
     (λ {Ε} {Φ} i₁ i₂ {s} S Suni → ≣-trans τ (≣-trans τ (≣-sym τ (≣-trans τ (≣-sym τ
       (≣-trans τ (weaken-eval i₁ t (Uniε-weaken Γ i₂ Runi , Suni))
       (≣-eval t (Uniε-weaken Γ i₁ (Uniε-weaken Γ i₂ Runi) , Uni-weaken σ i₁ Suni)
          (Uniε-weaken Γ (⊆-trans i₂ i₁) Runi , Uni-weaken σ i₁ Suni)
          (≣ε-weaken² Γ i₂ i₁ , ≣-refl σ _))))
       (≣-weaken τ i₁ (≣-trans τ (≣-coerce τ id (sym (trans (cong (λ t₁ → subst t₁ (s , Γ⊩ Ε))
          (weaken-subst (pop! i₂) t (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) ρ)))
          (trans (cong (λ ρ₁ → subst (subst t (var here! , ρ₁)) (s , Γ⊩ Ε))
          (trans (⊩-weaken² Γ (step (⊆-refl Δ)) (pop! i₂) ρ) (trans (cong (λ pr → ⊩-weaken Γ pr ρ)
          (⊆-step-same i₂))
          (sym (⊩-weaken² Γ i₂ (step (⊆-refl Ε)) ρ))))) (βsubst t s (⊩-weaken Γ i₂ ρ))))))
       (≣-⊩τ-◃ τ _ (red (weaken (pop! i₂) (subst t (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) ρ))) s))))))
       (≣-coerce τ id (sym (trans (cong (λ t₁ → subst t₁ (weaken i₁ s , Γ⊩ Φ)) (weaken-subst (pop! (⊆-trans i₂ i₁)) t
          (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) ρ))) (trans (cong (λ ρ₁ → subst (subst t (var here! , ρ₁))
          (weaken i₁ s , Γ⊩ Φ)) (trans (⊩-weaken² Γ (step (⊆-refl Δ)) (pop! (⊆-trans i₂ i₁)) ρ) (trans
          (cong (λ pr → ⊩-weaken Γ pr ρ) (⊆-step-same (⊆-trans i₂ i₁))) (sym (⊩-weaken² Γ (⊆-trans i₂ i₁)
          (step (⊆-refl Φ)) ρ))))) (βsubst t (weaken i₁ s) (⊩-weaken Γ (⊆-trans i₂ i₁) ρ)))))))
       (≣-⊩τ-◃ τ _ (red (weaken (pop! (⊆-trans i₂ i₁))
          (subst t (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) ρ))) (weaken i₁ s))))
    Uni-eval (app {σ} {τ} f x) {ρ}  Runi with Uni-eval f Runi | Uni-eval x Runi
    ... | h₁ , h₂ , h₃ | xuni =
      Uni-coerce τ (λ f₁ → app f₁ (subst x ρ)) (weaken-same (subst f ρ)) (h₁ (same _) (eval x _) xuni)

{- evaluation in semantically equal uniform environments yields
   semantically equal objects -}

  abstract

    ≣-eval : ∀ {Γ Δ σ} (t : Γ ⊢ σ) {ρ₁} {R₁ : Δ ⊩ε Γ [ ρ₁ ]} (Runi₁ : Uni[ Δ ,ε Γ ] R₁)
      {ρ₂} {R₂ : Δ ⊩ε Γ [ ρ₂ ]} (Runi₂ : Uni[ Δ ,ε Γ ] R₂) (eqR₁R₂ : [ Γ ] R₁ ≣ε R₂) →
      [ σ ] eval t R₁ ≣ eval t R₂
    ≣-eval (var pr) Runi₁ Runi₂ eqR₁R₂ = ≣-lookup pr eqR₁R₂
    ≣-eval {Γ} {Δ} (lam {σ} {τ} t) {ρ₁} Runi₁ {ρ₂} Runi₂ eqR₁R₂ =
      λ {Ε} inc {s} S Suni →
      ≣-trans τ (≣-sym τ (≣-⊩τ-◃ τ _ (red (weaken (pop! inc) (subst t (var here! ,
        ⊩-weaken Γ (step (same Δ)) ρ₁))) s)))
     (≣-trans τ (≣-sym τ (≣-coerce τ id (sym (trans (cong (λ t → subst t (s , Γ⊩ Ε))
          (weaken-subst (pop! inc) t (var here! , ⊩-weaken Γ (step (same Δ)) ρ₁)))
          (trans (cong (λ ρ → β-reduce (subst t (var here! , ρ)) s)
          (trans (⊩-weaken² Γ (step (same Δ)) (pop! inc) ρ₁)
          (trans (cong (λ pr → ⊩-weaken Γ pr ρ₁) (⊆-step-same inc))
          (sym (⊩-weaken² Γ inc (step (same Ε)) ρ₁))))) (βsubst t s (⊩-weaken Γ inc ρ₁)))))))
     (≣-trans τ (≣-eval t ((Uniε-weaken Γ inc Runi₁) , Suni) (Uniε-weaken Γ inc Runi₂ , Suni)
       (≣ε-weaken Γ inc eqR₁R₂ , ≣-refl σ S))
     (≣-trans τ (≣-coerce τ id (sym (trans (cong (λ t → subst t (s , Γ⊩ Ε))
          (weaken-subst (pop! inc) t (var here! , ⊩-weaken Γ (step (same Δ)) ρ₂)))
          (trans (cong (λ ρ → β-reduce (subst t (var here! , ρ)) s)
          (trans (⊩-weaken² Γ (step (same Δ)) (pop! inc) ρ₂)
          (trans (cong (λ pr → ⊩-weaken Γ pr ρ₂) (⊆-step-same inc))
          (sym (⊩-weaken² Γ inc (step (same Ε)) ρ₂))))) (βsubst t s (⊩-weaken Γ inc ρ₂))))))
     (≣-⊩τ-◃ τ _ (red (weaken (pop! inc) (subst t (var here! , ⊩-weaken Γ (step (same Δ)) ρ₂))) s)))))
    ≣-eval {Γ} {Δ} (app {σ} {τ} f x) {ρ₁} Runi₁ {ρ₂} Runi₂ eqR₁R₂ with Uni-eval f Runi₂
    ... | h₁ , h₂ , h₃ =
      ≣-trans τ (≣-sym τ (≣-coerce τ (λ f → app f (subst x ρ₁)) (weaken-same (subst f ρ₁))))
     (≣-trans τ (≣-trans τ (≣-eval f Runi₁ Runi₂ eqR₁R₂ (same Δ) _ (Uni-eval x Runi₁))
     (h₂ (same Δ) _ _ (Uni-eval x Runi₁) (Uni-eval x Runi₂) (≣-eval x Runi₁ Runi₂ eqR₁R₂)))
     (≣-coerce τ  (λ f → app f (subst x ρ₂)) (weaken-same (subst f ρ₂))))

{- weakening of evaluated is the same as evaluation in a weakened environment -}

  abstract

    weaken-eval : ∀ {Δ Ε} (inc : Δ ⊆ Ε) {Γ σ} (t : Γ ⊢ σ) {ρ} {R : Δ ⊩ε Γ [ ρ ]}
      (Runi : Uni[ Δ ,ε Γ ] R) → [ σ ] ⊩τ-weaken _ inc (eval t R) ≣ eval t (⊩ε-weaken Γ inc R)
    weaken-eval inc (var pr) Runi = weaken-lookup inc pr _
    weaken-eval {Δ} {Ε} inc {Γ} (lam {σ} {τ} t) {ρ} Runi =
      λ {Φ} inc' {s} S Suni →
      ≣-trans τ (≣-sym τ (≣-trans τ (≣-trans τ
      (≣-eval t (Uniε-weaken Γ inc' (Uniε-weaken Γ inc Runi) , Suni)
        (Uniε-weaken Γ (⊆-trans inc inc') Runi , Suni) (≣ε-weaken² Γ inc inc' , ≣-refl σ S))
      (≣-coerce τ id (sym (trans (cong (λ t₁ → subst t₁ (s , Γ⊩ Φ))
        (weaken-subst (pop! (⊆-trans inc inc')) t (var here! ,
        ⊩-weaken Γ (step (⊆-refl Δ)) ρ))) (trans (cong (λ ρ₁ → subst (subst t (var here! , ρ₁))
        (s , Γ⊩ Φ)) (trans (⊩-weaken² Γ (step (⊆-refl Δ)) (pop! (⊆-trans inc inc')) ρ)
        (trans (cong (λ pr → ⊩-weaken Γ pr ρ) (⊆-step-same (⊆-trans inc inc')))
        (sym (⊩-weaken² Γ (⊆-trans inc inc') (step (⊆-refl Φ)) ρ)))))
        (βsubst t s (⊩-weaken Γ (⊆-trans inc inc') ρ)))))))
      (≣-trans τ (≣-⊩τ-◃ τ _ (red (weaken (pop! (⊆-trans inc inc'))
         (subst t (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) ρ))) s))
      (≣-coerce τ (λ f → app f s) (sym (weaken² inc inc' (lam (subst t (var here! ,
         ⊩-weaken Γ (step (⊆-refl Δ)) ρ)))))))))
      (≣-trans τ (≣-coerce τ id (sym (trans (cong (λ t₁ → subst t₁ (s , Γ⊩ Φ))
         (weaken-subst (pop! inc') t (var here! , ⊩-weaken Γ (step (⊆-refl Ε))
         (⊩-weaken Γ inc ρ)))) (trans (cong (λ ρ₁ → subst (subst t (var here! , ρ₁)) (s , Γ⊩ Φ))
         (trans (⊩-weaken² Γ (step (⊆-refl Ε)) (pop! inc') (⊩-weaken Γ inc ρ))
         (trans (cong (λ pr → ⊩-weaken Γ pr (⊩-weaken Γ inc ρ)) (⊆-step-same inc'))
         (sym (⊩-weaken² Γ inc' (step (⊆-refl Φ)) (⊩-weaken Γ inc ρ))))))
         (βsubst t s (⊩-weaken Γ inc' (⊩-weaken Γ inc ρ)))))))
      (≣-⊩τ-◃ τ _ (red (weaken (pop! inc') (subst t (var here! ,
         ⊩-weaken Γ (step (⊆-refl Ε)) (⊩-weaken Γ inc ρ)))) s)))
    weaken-eval {Δ} {Ε} inc {Γ} (app {σ} {τ} f x) {ρ} {R} Runi with Uni-eval f Runi
    ... | h₁ , h₂ , h₃ =
      ≣-trans τ (≣-weaken τ inc (≣-sym τ (≣-coerce τ (λ f → app f (subst x ρ)) (weaken-same _))))
     (≣-trans τ (≣-trans τ (h₃ inc (same Δ) (eval x R) (Uni-eval x Runi))
     (≣-trans τ (≣-trans τ (coerce₂ (λ pr₁ pr₂ → [ τ ] eval f R pr₁ (⊩τ-weaken _ inc (eval x R)) ≣
         eval f R pr₂ (eval x (⊩ε-weaken Γ inc R)))
        (sym (⊆-same-l inc)) (sym (⊆-same-r inc)) (h₂ inc (⊩τ-weaken (subst x ρ) inc (eval x R))
        (eval x (⊩ε-weaken Γ inc R)) (Uni-weaken σ inc (Uni-eval x Runi))
        (Uni-eval x (Uniε-weaken Γ inc Runi)) (weaken-eval inc x Runi)))
     (≣-coerce τ (λ t → app t (subst x (⊩-weaken Γ inc ρ)))
        (sym (weaken² inc (⊆-refl Ε) (subst f ρ)))))
     (weaken-eval inc f Runi (⊆-refl Ε) (eval x (⊩ε-weaken Γ inc R))
        (Uni-eval x (Uniε-weaken Γ inc Runi)))))
     (≣-coerce τ (λ f → app f (subst x (⊩-weaken Γ inc ρ))) (weaken-same (subst f _))))

abstract

  ≣ε-eval : ∀ {Δ Ε} Γ (γ : Δ ⊩ Γ) {ρ₁} {R₁ : Ε ⊩ε Δ [ ρ₁ ]} (Runi₁ : Uni[ Ε ,ε Δ ] R₁)
      {ρ₂} {R₂ : Ε ⊩ε Δ [ ρ₂ ]} (Runi₂ : Uni[ Ε ,ε Δ ] R₂) (eqR₁R₂ : [ Δ ] R₁ ≣ε R₂) →
      [ Γ ] εeval Γ γ R₁ ≣ε εeval Γ γ R₂
  ≣ε-eval ε γ Runi₁ Runi₂ eqR₁R₂ = tt
  ≣ε-eval (Γ ∙ σ) (g , γ) Runi₁ Runi₂ eqR₁R₂ =
    ≣ε-eval Γ γ Runi₁ Runi₂ eqR₁R₂ , ≣-eval g Runi₁ Runi₂ eqR₁R₂

  weaken-εeval : ∀ Γ {Ε Φ} (inc : Ε ⊆ Φ) {Δ} (γ : Δ ⊩ Γ) {ρ} {R : Ε ⊩ε Δ [ ρ ]}
    (Runi : Uni[ Ε ,ε Δ ] R) → [ Γ ] ⊩ε-weaken Γ inc (εeval Γ γ R) ≣ε εeval Γ γ (⊩ε-weaken Δ inc R)
  weaken-εeval ε inc γ Runi = tt
  weaken-εeval (Γ ∙ σ) inc (g , γ) Runi = weaken-εeval Γ inc γ Runi , weaken-eval inc g Runi

abstract

  Uni-εpurge : ∀ {Γ Δ} (inc : Γ ⊆ Δ) {Ε ρ} {R : Ε ⊩ε Δ [ ρ ]}
    (Runi : Uni[ Ε ,ε Δ ] R) → Uni[ Ε ,ε Γ ] (εpurge inc R)
  Uni-εpurge base Runi = Runi
  Uni-εpurge (step inc) (Runi , runi) = Uni-εpurge inc Runi
  Uni-εpurge (pop! inc) (Runi , runi) = Uni-εpurge inc Runi , runi

  εpurge-refl : ∀ Γ {Δ} {ρ} (R : Δ ⊩ε Γ [ ρ ]) → [ Γ ] εpurge (same Γ) R ≣ε R
  εpurge-refl ε R = tt
  εpurge-refl (Γ ∙ σ) (r , R) = εpurge-refl Γ R , ≣-refl σ r

  εpurge-weaken : ∀ {Γ Δ} (inc : Γ ⊆ Δ) {Ε Φ} (inc' : Ε ⊆ Φ) {ρ} (R : Ε ⊩ε Δ [ ρ ]) →
    [ Γ ] εpurge inc (⊩ε-weaken Δ inc' R) ≣ε ⊩ε-weaken Γ inc' (εpurge inc R)
  εpurge-weaken base inc' R = R
  εpurge-weaken (step inc) inc' (r , R) = εpurge-weaken inc inc' R
  εpurge-weaken (pop! inc) inc' (r , R) = εpurge-weaken inc inc' R , ≣-refl _ _

  Uniε-eval : ∀ {Δ Ε} Γ (γ : Δ ⊩ Γ) {ρ} {R : Ε ⊩ε Δ [ ρ ]} (Runi : Uni[ Ε ,ε Δ ] R) →
              Uni[ Ε ,ε Γ ] (εeval Γ γ R)
  Uniε-eval ε γ Runi = tt
  Uniε-eval (Γ ∙ σ) (g , γ) Runi = Uniε-eval Γ γ Runi , Uni-eval g Runi

  lookup-purge : ∀ {Γ σ} (pr : σ ∈ Γ) {Δ} (inc : Γ ⊆ Δ) {Ε ρ} (R : Ε ⊩ε Δ [ ρ ]) →
    [ σ ] lookup (inc-in inc pr) R ≣ lookup pr (εpurge inc R)
  lookup-purge () base R
  lookup-purge pr (step inc) (_ , R) = lookup-purge pr inc R
  lookup-purge here! (pop! inc) (r , _) = ≣-refl _ r
  lookup-purge (there pr) (pop! inc) (_ , R) = lookup-purge pr inc R

  eval-weaken : ∀ {Γ σ} (t : Γ ⊢ σ) {Δ} (inc : Γ ⊆ Δ) {Ε ρ} {R : Ε ⊩ε Δ [ ρ ]}
    (Runi : Uni[ Ε ,ε Δ ] R) → [ σ ] eval (weaken inc t) R ≣ eval t (εpurge inc R)
  eval-weaken (var pr) inc Runi = lookup-purge pr inc _
  eval-weaken {Γ} (lam {σ} {τ} t) {Δ} inc {Ε} {ρ} {R} Runi =
    λ {Φ} inc' {s} S Suni →
    ≣-trans τ (≣-trans τ (≣-sym τ (≣-trans τ (≣-coerce τ id (sym
      (trans (cong (λ t₁ → subst t₁ (s , Γ⊩ Φ)) (weaken-subst (pop! inc')
      (weaken (pop! inc) t) (var here! , ⊩-weaken Δ (step (⊆-refl Ε)) ρ)))
      (trans (cong (λ ρ₁ → subst (subst (weaken (pop! inc) t) (var here! , ρ₁)) (s , Γ⊩ Φ))
      (trans (⊩-weaken² Δ (step (⊆-refl Ε)) (pop! inc') ρ)
      (trans (cong (λ pr → ⊩-weaken Δ pr ρ) (⊆-step-same inc'))
      (sym (⊩-weaken² Δ inc' (step (⊆-refl Φ)) ρ)))))
      (βsubst (weaken (pop! inc) t) s (⊩-weaken Δ inc' ρ))))))
   (≣-⊩τ-◃ τ _ (red (weaken (pop! inc') (subst (weaken (pop! inc) t) (var here! ,
      ⊩-weaken Δ (step (⊆-refl Ε)) ρ))) s))))
   (≣-trans τ (eval-weaken t (pop! inc) (Uniε-weaken Δ inc' Runi , Suni))
   (≣-eval t (Uni-εpurge inc (Uniε-weaken Δ inc' Runi) , Suni)
      (Uniε-weaken Γ inc' (Uni-εpurge inc Runi) , Suni)
      (εpurge-weaken inc inc' R , ≣-refl σ S))))
   (≣-trans τ (≣-coerce τ id (sym (trans (cong (λ t₁ → subst t₁ (s , Γ⊩ Φ))
      (weaken-subst (pop! inc') t (var here! , ⊩-weaken Γ (step (⊆-refl Ε)) (purge inc ρ))))
      (trans (cong (λ ρ₁ → subst (subst t (var here! , ρ₁)) (s , Γ⊩ Φ))
      (trans (⊩-weaken² Γ (step (⊆-refl Ε)) (pop! inc') (purge inc ρ))
      (trans (cong (λ pr → ⊩-weaken Γ pr (purge inc ρ)) (⊆-step-same inc'))
      (sym (⊩-weaken² Γ inc' (step (⊆-refl Φ)) (purge inc ρ))))))
      (βsubst t s (⊩-weaken Γ inc' (purge inc ρ)))))))
   (≣-⊩τ-◃ τ _ (red (weaken (pop! inc') (subst t (var here! ,
      ⊩-weaken Γ (step (⊆-refl Ε)) (purge inc ρ)))) s)))
  eval-weaken {Γ} (app {σ} {τ} f x) {Δ} inc {Ε} {ρ} {R} Runi with Uni-eval f (Uni-εpurge inc Runi)
  ... | h₁ , h₂ , h₃ =
    ≣-trans τ (≣-sym τ (≣-trans τ
   (≣-trans τ (h₂ _ _ _ (Uni-eval x (Uni-εpurge inc Runi)) (Uni-eval (weaken inc x) Runi)
      (≣-sym σ (eval-weaken x inc Runi)))
   (≣-sym τ (eval-weaken f inc Runi _ _ (Uni-eval (weaken inc x) Runi))))
   (≣-coerce τ (λ f → app f (subst (weaken inc x) ρ)) (weaken-same (subst (weaken inc f) ρ)))))
   (≣-coerce τ (λ f → app f (subst x (purge inc ρ))) (weaken-same (subst f (purge inc ρ))))

  εeval-weaken : ∀ {Δ} Γ {γ : Δ ⊩ Γ} {Ε} (inc : Δ ⊆ Ε) {Φ ρ} {R : Φ ⊩ε Ε [ ρ ]}
    (Runi : Uni[ Φ ,ε Ε ] R) → [ Γ ] εeval Γ (⊩-weaken Γ inc γ) R ≣ε εeval Γ γ (εpurge inc R)
  εeval-weaken ε inc Runi = tt
  εeval-weaken (Γ ∙ σ) {g , γ} inc Runi = εeval-weaken Γ inc Runi , eval-weaken g inc Runi

  εeval-Γ⊩ : ∀ Γ {Δ} {ρ} {R : Δ ⊩ε Γ [ ρ ]} (Runi : Uni[ Δ ,ε Γ ] R) → [ Γ ] εeval Γ (Γ⊩ Γ) R ≣ε R
  εeval-Γ⊩ ε Runi = tt
  εeval-Γ⊩ (Γ ∙ σ) (Runi , runi) =
    ≣ε-trans Γ (εeval-weaken Γ (step (⊆-refl Γ)) (Runi , runi))
   (≣ε-trans Γ (≣ε-eval Γ (Γ⊩ Γ) (Uni-εpurge (⊆-refl Γ) Runi) Runi (εpurge-refl Γ _))
   (εeval-Γ⊩ Γ Runi)) , ≣-refl σ _

abstract

  eval-get : ∀ {Γ Δ Ε σ} (pr : σ ∈ Γ) {γ : Δ ⊩ Γ} {ρ} {R : Ε ⊩ε Δ [ ρ ]} →
    [ σ ] eval (get pr γ) R ≣ lookup pr (εeval Γ γ R)
  eval-get here! = ≣-refl _ _
  eval-get (there pr) = eval-get pr

  eval-subst : ∀ {Γ Δ Ε σ} (t : Γ ⊢ σ) {γ : Δ ⊩ Γ} {ρ} {R : Ε ⊩ε Δ [ ρ ]}
    (Runi : Uni[ Ε ,ε Δ ] R) → [ σ ] eval (subst t γ) R ≣ eval t (εeval Γ γ R)
  eval-subst (var pr) Runi = eval-get pr
  eval-subst {Γ} {Δ} {Ε} (lam {σ} {τ} t) {γ} {ρ} {R} Runi =
    λ {Φ} inc {s} S Suni →
    ≣-trans τ (≣-trans τ (≣-sym τ (≣-trans τ (≣-coerce τ id (sym
       (trans (cong (λ t₁ → subst t₁ (s , Γ⊩ Φ)) (weaken-subst (pop! inc)
       (subst t (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) γ))
       (var here! , ⊩-weaken Δ (step (⊆-refl Ε)) ρ)))
       (trans (cong (λ ρ₁ → subst (subst (subst t (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) γ))
       (var here! , ρ₁)) (s , Γ⊩ Φ)) (trans (⊩-weaken² Δ (step (⊆-refl Ε)) (pop! inc) ρ)
       (trans (cong (λ pr → ⊩-weaken Δ pr ρ) (⊆-step-same inc))
       (sym (⊩-weaken² Δ inc (step (⊆-refl Φ)) ρ)))))
       (βsubst (subst t (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) γ)) s (⊩-weaken Δ inc ρ))))))
   (≣-⊩τ-◃ τ _ (red (weaken (pop! inc) (subst (subst t (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) γ))
      (var here! , ⊩-weaken Δ (step (⊆-refl Ε)) ρ))) s))))
   (≣-trans τ (eval-subst t (Uniε-weaken Δ inc Runi , Suni))
   (≣-eval t ((Uniε-eval Γ (⊩-weaken Γ (step (⊆-refl Δ)) γ) (Uniε-weaken Δ inc Runi , Suni)) , Suni)
      (Uniε-weaken Γ inc (Uniε-eval Γ γ Runi) , Suni)
      (≣ε-sym Γ (≣ε-trans Γ (weaken-εeval Γ inc γ Runi) (≣ε-trans Γ (≣ε-eval Γ γ
      (Uniε-weaken Δ inc Runi) (Uni-εpurge (⊆-refl Δ) (Uniε-weaken Δ inc Runi))
      (≣ε-sym Δ (εpurge-refl Δ (⊩ε-weaken Δ inc R)))) (≣ε-sym Γ (εeval-weaken Γ (step (⊆-refl Δ))
      ((Uniε-weaken Δ inc Runi) , Suni))))) , ≣-refl σ S))))
   (≣-trans τ (≣-coerce τ id (sym (trans (cong (λ t₁ → subst t₁ (s , Γ⊩ Φ))
      (weaken-subst (pop! inc) t (var here! , ⊩-weaken Γ (step (⊆-refl Ε)) (⊩² Γ γ ρ))))
      (trans (cong (λ ρ₁ → subst (subst t (var here! , ρ₁)) (s , Γ⊩ Φ))
      (trans (⊩-weaken² Γ (step (⊆-refl Ε)) (pop! inc) (⊩² Γ γ ρ))
      (trans (cong (λ pr → ⊩-weaken Γ pr (⊩² Γ γ ρ)) (⊆-step-same inc))
      (sym (⊩-weaken² Γ inc (step (⊆-refl Φ)) (⊩² Γ γ ρ))))))
      (βsubst t s (⊩-weaken Γ inc (⊩² Γ γ ρ)))))))
   (≣-⊩τ-◃ τ _ (red (weaken (pop! inc) (subst t (var here! ,
      ⊩-weaken Γ (step (⊆-refl Ε)) (⊩² Γ γ ρ)))) s)))
  eval-subst {Γ} {Δ} {Ε} (app {σ} {τ} f x) {γ} {ρ} {R} Runi with Uni-eval f (Uniε-eval Γ γ Runi)
  ... | h₁ , h₂ , h₃ =
    ≣-trans τ (≣-sym τ (≣-coerce τ (λ f → app f (subst (subst x γ) ρ))
      (weaken-same (subst (subst f γ) ρ))))
   (≣-trans τ (≣-trans τ (eval-subst f Runi (⊆-refl Ε) (eval (subst x γ) R)
      (Uni-eval (subst x γ) Runi))
   (h₂ (⊆-refl Ε) (eval (subst x γ) R) (eval x (εeval Γ γ R))
      (Uni-eval (subst x γ) Runi) (Uni-eval x (Uniε-eval Γ γ Runi)) (eval-subst x Runi)))
   (≣-coerce τ (λ f → app f (subst x (⊩² Γ γ ρ))) (weaken-same (subst f (⊩² Γ γ ρ)))))

abstract

  ≣-red : ∀ {Γ σ s t} (r : Γ ⊢ σ ∋ s ▹ t) {Δ ρ} {R : Δ ⊩ε Γ [ ρ ]}
    (Runi : Uni[ Δ ,ε Γ ] R) → [ σ ] eval s R ≣ eval t R
  ≣-red {Γ} (lam {σ} {τ} {f} {g} r) {Δ} {ρ} Runi =
    λ {Ε} inc {s} S Suni →
    ≣-trans τ (≣-sym τ (≣-trans τ (≣-sym τ (≣-red r (Uniε-weaken Γ inc Runi , Suni)))
   (≣-trans τ (≣-coerce τ id (sym (trans (cong (λ t → subst t (s , Γ⊩ Ε))
      (weaken-subst (pop! inc) f (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) ρ)))
      (trans (cong (λ ρ₁ → subst (subst f (var here! , ρ₁)) (s , Γ⊩ Ε))
      (trans (⊩-weaken² Γ (step (⊆-refl Δ)) (pop! inc) ρ)
      (trans (cong (λ pr → ⊩-weaken Γ pr ρ) (⊆-step-same inc))
      (sym (⊩-weaken² Γ inc (step (⊆-refl Ε)) ρ)))))
      (βsubst f s (⊩-weaken Γ inc ρ))))))
   (≣-⊩τ-◃ τ _ (red (weaken (pop! inc) (subst f (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) ρ))) s)))))
   (≣-trans τ (≣-coerce τ id (sym (trans (cong (λ t → subst t (s , Γ⊩ Ε))
      (weaken-subst (pop! inc) g (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) ρ)))
      (trans (cong (λ ρ₁ → subst (subst g (var here! , ρ₁)) (s , Γ⊩ Ε))
      (trans (⊩-weaken² Γ (step (⊆-refl Δ)) (pop! inc) ρ)
      (trans (cong (λ pr → ⊩-weaken Γ pr ρ) (⊆-step-same inc))
      (sym (⊩-weaken² Γ inc (step (⊆-refl Ε)) ρ)))))
      (βsubst g s (⊩-weaken Γ inc ρ))))))
   (≣-⊩τ-◃ τ _ (red (weaken (pop! inc) (subst g (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) ρ))) s)))
  ≣-red {Γ} (eta {σ} {τ} {t}) {Δ} {ρ} {R} Runi =
    λ {Ε} inc {s} S Suni →
    let hs : Uni[ Δ , σ ▹ τ ] (eval t R)
        hs = Uni-eval t Runi in
    ≣-trans τ (≣-trans τ (≣-trans τ (≣-trans τ
   (coerce (λ pr → [ τ ] eval t R inc S ≣ eval t R pr S) (sym (⊆-same-r inc)) (≣-refl τ _))
   (≣-coerce τ (λ f → app f s) (sym (weaken² inc (⊆-refl Ε) (subst t ρ)))))
   (≣-trans τ (weaken-eval inc t Runi (same _) S Suni)
   (≣-eval t (Uniε-weaken Γ inc Runi) (Uni-εpurge (⊆-refl Γ) (Uniε-weaken Γ inc Runi))
      (≣ε-sym Γ (εpurge-refl Γ (⊩ε-weaken Γ inc R))) (same _) S Suni)))
   (≣-sym τ (eval-weaken t (step (⊆-refl Γ)) (Uniε-weaken Γ inc Runi , Suni) _ S Suni)))
   (≣-trans τ (≣-trans τ (≣-coerce τ (λ f → app f s) (weaken-same
      (subst (weaken (step (⊆-refl Γ)) t) (s , ⊩-weaken Γ inc ρ))))
   (≣-coerce τ id (sym (trans (cong (λ t₁ → subst t₁ (s , Γ⊩ Ε)) (weaken-subst (pop! inc)
      (app (weaken (step (⊆-refl Γ)) t) (var here!)) (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) ρ)))
      (trans (cong (λ ρ₁ → app (subst (subst (weaken (step (⊆-refl Γ)) t) (var here! , ρ₁))
      (s , Γ⊩ Ε)) s) (trans (⊩-weaken² Γ (step (⊆-refl Δ)) (pop! inc) ρ)
      (trans (cong (λ pr → ⊩-weaken Γ pr ρ) (⊆-step-same inc))
      (sym (⊩-weaken² Γ inc (step (⊆-refl Ε)) ρ)))))
      (βsubst (app (weaken (step (⊆-refl Γ)) t) (var here!)) s (⊩-weaken Γ inc ρ)))))))
   (≣-⊩τ-◃ τ _ (red (app (weaken (pop! inc) (subst (weaken (step (⊆-refl Γ)) t)
      (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) ρ))) (var here!)) s)))
  ≣-red {Γ} (apl {σ} {τ} {f} {g} {x} r) {Δ} {ρ} {R} Runi =
    ≣-trans τ (≣-sym τ (≣-coerce τ (λ f → app f (subst x ρ)) (weaken-same (subst f ρ))))
   (≣-trans τ (≣-red r Runi (⊆-refl Δ) (eval x R) (Uni-eval x Runi))
   (≣-coerce τ (λ f → app f (subst x ρ)) (weaken-same (subst g ρ))))
  ≣-red (apr {σ} {τ} {f} {x} {y} r) {Δ} {ρ} {R} Runi with Uni-eval f Runi
  ... | h₁ , h₂ , h₃ =
    ≣-trans τ (≣-sym τ (≣-coerce τ (λ f → app f (subst x ρ)) (weaken-same (subst f ρ))))
   (≣-trans τ (h₂ (⊆-refl Δ) (eval x R) (eval y R) (Uni-eval x Runi) (Uni-eval y Runi)
     (≣-red r Runi))
   (≣-coerce τ (λ f → app f (subst y ρ)) (weaken-same (subst f ρ))))
  ≣-red {Γ} (red {σ} {τ} t s) {Δ} {ρ} {R} Runi =
    ≣-sym τ (≣-trans τ (≣-trans τ (eval-subst t Runi)
   (≣-eval t (Uniε-eval Γ (Γ⊩ Γ) Runi , Uni-eval s Runi)
      (Uniε-weaken Γ (⊆-refl Δ) Runi , Uni-eval s Runi)
      (≣ε-trans Γ (εeval-Γ⊩ Γ Runi) (≣ε-weaken-refl Γ R) , ≣-refl σ (eval s R))))
   (≣-trans τ (≣-coerce τ id (sym (trans (cong (λ t₁ → subst t₁ (subst s ρ , Γ⊩ Δ))
      (weaken-subst (pop! (⊆-refl Δ)) t (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) ρ)))
      (trans (cong (λ ρ₁ → subst (subst t (var here! , ρ₁)) (subst s ρ , Γ⊩ Δ))
      (trans (⊩-weaken² Γ (step (⊆-refl Δ)) (pop! (⊆-refl Δ)) ρ)
      (trans (cong (λ pr → ⊩-weaken Γ pr ρ) (⊆-step-same (⊆-refl Δ)))
      (sym (⊩-weaken² Γ (⊆-refl Δ) (step (⊆-refl Δ)) ρ)))))
      (βsubst t (subst s ρ) (⊩-weaken Γ (⊆-refl Δ) ρ)))))) 
   (≣-trans τ (≣-⊩τ-◃ τ _ (red (weaken (pop! (⊆-refl Δ))
      (subst t (var here! , ⊩-weaken Γ (step (⊆-refl Δ)) ρ))) (subst s ρ)))
   (≣-coerce τ (λ f → app f (subst s ρ)) (weaken-same (lam (subst t (var here! ,
      ⊩-weaken Γ (step (⊆-refl Δ)) ρ))))))))

  ≣-reds : ∀ {σ Γ} {s t : Γ ⊢ σ} (r : s ≡βη t) {Δ ρ} {R : Δ ⊩ε Γ [ ρ ]}
      (Runi : Uni[ Δ ,ε Γ ] R) → [ σ ] eval s R ≣ eval t R
  ≣-reds {σ} refl Runi = ≣-refl σ _
  ≣-reds {σ} (lstep p r) Runi = ≣-trans σ (≣-red p Runi) (≣-reds r Runi)
  ≣-reds {σ} (rstep p r) Runi = ≣-trans σ (≣-sym σ (≣-red p Runi)) (≣-reds r Runi)

  completeness : ∀ {σ Γ} {s t : Γ ⊢ σ} (req : s ≡βη t) → norm s ≡ norm t
  completeness {σ} {Γ} {s} {t} req =
    cong back-nf (≣-≡nf σ
   (≣-trans σ (≣-sym σ (≣-coerce σ id (subst-Γ⊩ s)))
   (≣-trans σ (≣-reds req (Uni-Γ⊩ Γ))
   (≣-coerce σ id (subst-Γ⊩ t)))))