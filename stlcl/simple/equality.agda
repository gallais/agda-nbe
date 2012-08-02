module stlcl.simple.equality where

open import Data.Unit
open import Data.Product
open import Relation.Binary.PropositionalEquality renaming (subst to coerce ; subst₂ to coerce₂)

open import tools.contexts
open import tools.closures
open import stlcl.definition
open import stlcl.normalforms
open import stlcl.simple.model
open import stlcl.simple.eval

{- definition of semantical equality (extensional) and uniformity -}

infix 3 [_]_≣_ [_,_]_≣list≣_ [_]_≣ε_

data [_,_]_≣list≣_ {Γ} σ (Σ : ∀ {Δ} (S T : Δ ⊩ σ) → Set) : (XS YS : Γ ⊩ `list σ) → Set where
  `[] : [ σ , Σ ] `[] ≣list≣ `[]
  _`∷_  : ∀ {X Y} {XS YS : Γ ⊩ `list σ} (hd : Σ X Y) (tl : [ σ , Σ ] XS ≣list≣ YS) →
    [ σ , Σ ] X `∷ XS ≣list≣ Y `∷ YS
  mappend : ∀ {τ} {F₁ F₂ : ∀ {Δ} (inc : Γ ⊆ Δ) (t : Δ ⊢ne τ) → Δ ⊩ σ} {xs₁ xs₂ YS₁ YS₂}
    (F : ∀ {Δ} inc (t : Δ ⊢ne τ) → Σ (F₁ inc t) (F₂ inc t))
    (xs : xs₁ ≡ xs₂) (YS : [ σ , Σ ] YS₁ ≣list≣ YS₂) →
    [ σ , Σ ] mappend F₁ xs₁ YS₁ ≣list≣ mappend F₂ xs₂ YS₂

mutual

  [_]_≣_ : ∀ {Γ} σ (S T : Γ ⊩ σ) → Set
  [ `1 ] S ≣ T = ⊤
  [ σ `× τ ] S₁ , S₂ ≣ T₁ , T₂ = [ σ ] S₁ ≣ T₁ × [ τ ] S₂ ≣ T₂
  [ σ `→ τ ] F ≣ G = ∀ {Δ} inc (S : Δ ⊩ σ) (Suni : Uni[ σ ] S) → [ τ ] F inc S ≣ G inc S
  [ `list σ ] XS ≣ YS = [ σ , [_]_≣_ σ ] XS ≣list≣ YS

  Unilist[_]_ : ∀ {Γ} σ (S : Γ ⊩ `list σ) → Set
  Unilist[ σ ] `[] = ⊤
  Unilist[ σ ] (HD `∷ XS) = Uni[ σ ] HD × Unilist[ σ ] XS
  Unilist[_]_ {Γ} σ (mappend {τ} F xs XS) =
    ((∀ {Δ} inc t → Uni[ σ ] (F {Δ} inc t)) ×
    (∀ {Δ} {Ε} (i₁ : Δ ⊆ Ε) (i₂ : Γ ⊆ Δ) (t : Δ ⊢ne τ) →
    [ σ ] ⊩-weaken σ i₁ (F i₂ t) ≣ F (⊆-trans i₂ i₁) (ne-weaken i₁ t))) ×
    Unilist[ σ ] XS

  Uni[_]_ : ∀ {Γ} σ (S : Γ ⊩ σ) → Set
  Uni[ `1 ] S = ⊤
  Uni[ σ `× τ ] (A , B) = Uni[ σ ] A × Uni[ τ ] B
  Uni[_]_ {Γ} (σ `→ τ) F =
    (∀ {Δ} (inc : Γ ⊆ Δ) (S : Δ ⊩ σ) (Suni : Uni[ σ ] S) → Uni[ τ ] F inc S) ×
    (∀ {Δ} (inc : Γ ⊆ Δ) {S₁ S₂ : Δ ⊩ σ} (Suni₁ : Uni[ σ ] S₁) (Suni₂ : Uni[ σ ] S₂)
       (eq : [ σ ] S₁ ≣ S₂) → [ τ ] F inc S₁ ≣ F inc S₂) ×
    (∀ {Δ} {Ε} (i₁ : Δ ⊆ Ε) (i₂ : Γ ⊆ Δ) (S : Δ ⊩ σ) (Suni : Uni[ σ ] S) →
       [ τ ] ⊩-weaken τ i₁ (F i₂ S) ≣ F (⊆-trans i₂ i₁) (⊩-weaken σ i₁ S))
  Uni[ `list σ ] XS = Unilist[ σ ] XS


[_]_≣ε_ : ∀ {Δ} Γ (G R : Δ ⊩ε Γ) → Set
[ ε ] G ≣ε R = ⊤
[ Γ ∙ σ ] G , g ≣ε R , r = [ Γ ] G ≣ε R × [ σ ] g ≣ r

Uni[_]ε_ : ∀ {Δ} Γ (G : Δ ⊩ε Γ) → Set
Uni[ ε ]ε G = ⊤
Uni[ Γ ∙ σ ]ε (G , g) = Uni[ Γ ]ε G × Uni[ σ ] g

{- This extensional equality on semantical objects is an equivalence
   relation! And the same applies for its extension to contexts. -}

mutual

  abstract

    ≣list-refl : ∀ {Γ} σ (XS : Γ ⊩ `list σ) → [ `list σ ] XS ≣ XS
    ≣list-refl σ `[] = `[]
    ≣list-refl σ (HD `∷ TL) = ≣-refl σ HD `∷ ≣list-refl σ TL
    ≣list-refl σ (mappend F xs YS) = mappend (λ _ _ → ≣-refl σ _) refl (≣list-refl σ YS)

    ≣-refl : ∀ {Γ} σ (S : Γ ⊩ σ) → [ σ ] S ≣ S
    ≣-refl `1 S = tt
    ≣-refl (σ `× τ) (A , B) = ≣-refl σ A , ≣-refl τ B
    ≣-refl (σ `→ τ) F = λ inc S Suni → ≣-refl τ (F inc S)
    ≣-refl (`list σ) XS = ≣list-refl σ XS

mutual

  abstract

    ≣list-sym : ∀ {Γ} σ {S T : Γ ⊩ `list σ} (eq : [ `list σ ] S ≣ T) → [ `list σ ] T ≣ S
    ≣list-sym σ `[] = `[]
    ≣list-sym σ (hd `∷ tl) = ≣-sym σ hd `∷ ≣list-sym σ tl
    ≣list-sym σ (mappend F xs YS) = mappend (λ inc t → ≣-sym σ (F inc t)) (sym xs) (≣list-sym σ YS)

    ≣-sym : ∀ {Γ} σ {S T : Γ ⊩ σ} (eq : [ σ ] S ≣ T) → [ σ ] T ≣ S
    ≣-sym `1 eq = tt
    ≣-sym (σ `× τ) (eq₁ , eq₂) = ≣-sym σ eq₁ , ≣-sym τ eq₂
    ≣-sym (σ `→ τ) eq = λ inc S Suni → ≣-sym τ (eq inc S Suni)
    ≣-sym (`list σ) eq = ≣list-sym σ eq

mutual

  abstract

    ≣list-trans : ∀ {Γ} σ {S T U : Γ ⊩ `list σ} (eqST : [ `list σ ] S ≣ T)
      (eqTU : [ `list σ ] T ≣ U) → [ `list σ ] S ≣ U
    ≣list-trans σ `[] `[] = `[]
    ≣list-trans σ (hd₁ `∷ eqST) (hd₂ `∷ eqTU) = ≣-trans σ hd₁ hd₂ `∷ ≣list-trans σ eqST eqTU
    ≣list-trans σ (mappend F₁ xs₁ eqST) (mappend F₂ xs₂ eqTU) =
      mappend (λ inc t → ≣-trans σ (F₁ inc t) (F₂ inc t)) (trans xs₁ xs₂) (≣list-trans σ eqST eqTU)

    ≣-trans : ∀ {Γ} σ {S T U : Γ ⊩ σ} (eqST : [ σ ] S ≣ T) (eqTU : [ σ ] T ≣ U) → [ σ ] S ≣ U
    ≣-trans `1 eqST eqTU = tt
    ≣-trans (σ `× τ) (eqST₁ , eqST₂) (eqTU₁ , eqTU₂) = ≣-trans σ eqST₁ eqTU₁ , ≣-trans τ eqST₂ eqTU₂
    ≣-trans (σ `→ τ) eqST eqTU = λ inc S Suni → ≣-trans τ (eqST inc S Suni) (eqTU inc S Suni)
    ≣-trans (`list σ) eqST eqTU = ≣list-trans σ eqST eqTU

abstract

  ≣ε-refl : ∀ {Δ} Γ (R : Δ ⊩ε Γ) → [ Γ ] R ≣ε R
  ≣ε-refl ε R = tt
  ≣ε-refl (Γ ∙ σ) (G , g) = ≣ε-refl Γ G , ≣-refl σ g

  ≣ε-sym : ∀ {Δ} Γ {G R : Δ ⊩ε Γ} (eq : [ Γ ] G ≣ε R) → [ Γ ] R ≣ε G
  ≣ε-sym ε eq = tt
  ≣ε-sym (Γ ∙ σ) (eqGR , eqgr) = ≣ε-sym Γ eqGR , ≣-sym σ eqgr

  ≣ε-trans : ∀ {Δ} Γ {G R V : Δ ⊩ε Γ} (eqGR : [ Γ ] G ≣ε R) (eqRV : [ Γ ] R ≣ε V) → [ Γ ] G ≣ε V
  ≣ε-trans ε eqGR eqRV = tt
  ≣ε-trans (Γ ∙ σ) (eqGR , eqgr) (eqRV , eqrv) = ≣ε-trans Γ eqGR eqRV , ≣-trans σ eqgr eqrv

{- Using these results we build an equational reasoning
   apparatus allowing clearer proofs. -}

infix  3 _⊩_∋_Qed _⊩ε_∋_Qed
infixr 2 _⊩_∋_≡⟨_⟩_ _⊩_∋_≣⟨_⟩_ _⊩ε_∋_≡⟨_⟩_ _⊩ε_∋_≣⟨_⟩_
infix  1 Begin[_⊩_]_ Begin[_⊩ε_]_

Begin[_⊩_]_ : ∀ Γ σ {S T : Γ ⊩ σ} (eq : [ σ ] S ≣ T) → [ σ ] S ≣ T
Begin[ Γ ⊩ σ ] eq = eq

_⊩_∋_≡⟨_⟩_ : ∀ Γ σ S {T U : Γ ⊩ σ} (eq : S ≡ T) (eq' : [ σ ] T ≣ U) → [ σ ] S ≣ U
Γ ⊩ σ ∋ S ≡⟨ refl ⟩ eq = eq

_⊩_∋_≣⟨_⟩_ : ∀ Γ σ (S : Γ ⊩ σ) {T U : Γ ⊩ σ} (eq : [ σ ] S ≣ T) (eq' : [ σ ] T ≣ U) → [ σ ] S ≣ U
Γ ⊩ σ ∋ S ≣⟨ eq ⟩ eq' = ≣-trans σ eq eq'

_⊩_∋_Qed : ∀ Γ σ (S : Γ ⊩ σ) → [ σ ] S ≣ S
Γ ⊩ σ ∋ S Qed = ≣-refl σ S

Begin[_⊩ε_]_ : ∀ Γ σ {S T : Γ ⊩ε σ} (eq : [ σ ] S ≣ε T) → [ σ ] S ≣ε T
Begin[ Γ ⊩ε σ ] eq = eq

_⊩ε_∋_≡⟨_⟩_ : ∀ Γ σ S {T U : Γ ⊩ε σ} (eq : S ≡ T) (eq' : [ σ ] T ≣ε U) → [ σ ] S ≣ε U
Γ ⊩ε σ ∋ S ≡⟨ refl ⟩ eq = eq

_⊩ε_∋_≣⟨_⟩_ : ∀ Γ σ (S : Γ ⊩ε σ) {T U : Γ ⊩ε σ} (eq : [ σ ] S ≣ε T) (eq' : [ σ ] T ≣ε U) →
   [ σ ] S ≣ε U
Γ ⊩ε σ ∋ S ≣⟨ eq ⟩ eq' = ≣ε-trans σ eq eq'

_⊩ε_∋_Qed : ∀ Γ σ (S : Γ ⊩ε σ) → [ σ ] S ≣ε S
Γ ⊩ε σ ∋ S Qed = ≣ε-refl σ S

{- Weakening fusion laws for semantical objects -}

mutual

  abstract

    ≣list-weaken : ∀ {Γ Δ} σ {S T : Γ ⊩ `list σ} (inc : Γ ⊆ Δ) (eq : [ `list σ ] S ≣ T) →
      [ `list σ ] ⊩-weaken (`list σ) inc S ≣ ⊩-weaken (`list σ) inc T
    ≣list-weaken σ inc `[] = `[]
    ≣list-weaken σ inc (hd `∷ eq) = ≣-weaken σ inc hd `∷ ≣list-weaken σ inc eq
    ≣list-weaken σ inc (mappend F refl eq) =
      mappend (λ inc' t → F (⊆-trans inc inc') t) refl (≣list-weaken σ inc eq)

    ≣-weaken : ∀ {Γ Δ} σ {S T : Γ ⊩ σ} (inc : Γ ⊆ Δ) (eq : [ σ ] S ≣ T) →
      [ σ ] ⊩-weaken σ inc S ≣ ⊩-weaken σ inc T
    ≣-weaken `1 inc eq = eq
    ≣-weaken (σ `× τ) inc (eq₁ , eq₂) = ≣-weaken σ inc eq₁ , ≣-weaken τ inc eq₂
    ≣-weaken (σ `→ τ) inc eq = λ inc' S Suni → eq (⊆-trans inc inc') S Suni
    ≣-weaken (`list σ) inc eq = ≣list-weaken σ inc eq

mutual

  abstract

    ≣list-weaken-refl : ∀ {Γ} σ (S : Γ ⊩ `list σ) → [ `list σ ] S ≣ ⊩-weaken (`list σ) (same _) S
    ≣list-weaken-refl σ `[] = `[]
    ≣list-weaken-refl σ (HD `∷ TL) = ≣-weaken-refl σ HD `∷ ≣list-weaken-refl σ TL
    ≣list-weaken-refl σ (mappend F xs YS) =
      mappend
      (λ {Δ} inc t →
        Begin[ Δ ⊩ σ ]
          Δ ⊩ σ ∋ F inc t
          ≡⟨ cong (λ pr → F pr t) (sym (⊆-same-l inc)) ⟩
          Δ ⊩ σ ∋ F (⊆-trans (same _) inc) t
        Qed)
      (sym (ne-weaken-refl xs)) (≣list-weaken-refl σ YS)

    ≣-weaken-refl : ∀ {Γ} σ (S : Γ ⊩ σ) → [ σ ] S ≣ ⊩-weaken σ (same _) S
    ≣-weaken-refl `1 S = tt
    ≣-weaken-refl (σ `× τ) (A , B) = ≣-weaken-refl σ A , ≣-weaken-refl τ B
    ≣-weaken-refl (σ `→ τ) F =
      λ inc S Suni → coerce (λ pr → [ τ ] F inc S ≣ F pr S) (sym (⊆-same-l inc))
     (≣-refl τ (F inc S))
    ≣-weaken-refl (`list σ) XS = ≣list-weaken-refl σ XS

mutual

  abstract

    ≣list-weaken² : ∀ σ {Γ Δ} (inc : Γ ⊆ Δ) {Ε} (inc' : Δ ⊆ Ε) (S : Γ ⊩ `list σ) →
      [ `list σ ] ⊩-weaken (`list σ) inc' (⊩-weaken (`list σ) inc S) 
      ≣ ⊩-weaken (`list σ) (⊆-trans inc inc') S
    ≣list-weaken² σ inc inc' `[] = `[]
    ≣list-weaken² σ inc inc' (HD `∷ TL) = ≣-weaken² σ inc inc' HD `∷ ≣list-weaken² σ inc inc' TL
    ≣list-weaken² σ inc inc' (mappend F xs YS) =
      mappend
      (λ {Δ} inc'' t → 
      Begin[ Δ ⊩ σ ]
        Δ ⊩ σ ∋ F (⊆-trans inc (⊆-trans inc' inc'')) t
        ≡⟨ cong (λ pr → F pr t) (⊆-assoc inc inc' inc'') ⟩
        Δ ⊩ σ ∋ F (⊆-trans (⊆-trans inc inc') inc'') t
      Qed)
      (ne-weaken² inc inc' xs) (≣list-weaken² σ inc inc' YS)

    ≣-weaken² : ∀ σ {Γ Δ} (inc : Γ ⊆ Δ) {Ε} (inc' : Δ ⊆ Ε) (S : Γ ⊩ σ) →
      [ σ ] ⊩-weaken σ inc' (⊩-weaken σ inc S) ≣ ⊩-weaken σ (⊆-trans inc inc') S
    ≣-weaken² `1 inc inc' S = tt
    ≣-weaken² (σ `× τ) inc inc' (A , B) = ≣-weaken² σ inc inc' A , ≣-weaken² τ inc inc' B
    ≣-weaken² (σ `→ τ) inc inc' F =
      λ {Ε} inc'' S Suni →
      Begin[ Ε ⊩ τ ]
        Ε ⊩ τ ∋ F (⊆-trans inc (⊆-trans inc' inc'')) S
        ≡⟨ cong (λ pr → F pr S) (⊆-assoc inc inc' inc'') ⟩
        Ε ⊩ τ ∋ F (⊆-trans (⊆-trans inc inc') inc'') S
      Qed
    ≣-weaken² (`list σ) inc inc' XS = ≣list-weaken² σ inc inc' XS

abstract

  ≣ε-weaken : ∀ {Δ Ε} Γ {G R : Δ ⊩ε Γ} (inc : Δ ⊆ Ε) (eq : [ Γ ] G ≣ε R) →
      [ Γ ] ⊩ε-weaken Γ inc G ≣ε ⊩ε-weaken Γ inc R
  ≣ε-weaken ε inc eq = eq
  ≣ε-weaken (Γ ∙ σ) inc (eqGR , eqgr) = ≣ε-weaken Γ inc eqGR , ≣-weaken σ inc eqgr

  ≣ε-weaken-refl : ∀ {Δ} Γ (R : Δ ⊩ε Γ) → [ Γ ] R ≣ε ⊩ε-weaken Γ (same _) R
  ≣ε-weaken-refl ε R = R
  ≣ε-weaken-refl (Γ ∙ σ) (R , r) = ≣ε-weaken-refl Γ R , ≣-weaken-refl σ r

  ≣ε-weaken² : ∀ Γ {Δ Ε} (inc : Δ ⊆ Ε) {Φ} (inc' : Ε ⊆ Φ) (R : Δ ⊩ε Γ) →
      [ Γ ] ⊩ε-weaken Γ inc' (⊩ε-weaken Γ inc R) ≣ε ⊩ε-weaken Γ (⊆-trans inc inc') R
  ≣ε-weaken² ε inc inc' R = R
  ≣ε-weaken² (Γ ∙ σ) inc inc' (R , r) = ≣ε-weaken² Γ inc inc' R , ≣-weaken² σ inc inc' r

{- Uniformity is compatible with weakening -}

mutual

  abstract

    Unilist-weaken : ∀ {Γ Δ} σ (inc : Γ ⊆ Δ) (S : Γ ⊩ `list σ) (Suni : Uni[ `list σ ] S) →
      Uni[ `list σ ] ⊩-weaken (`list σ) inc S
    Unilist-weaken σ inc (`[]) Suni = Suni
    Unilist-weaken σ inc (HD `∷ S) (HDuni , Suni) =
      Uni-weaken σ inc HDuni , Unilist-weaken σ inc S Suni
    Unilist-weaken σ inc (mappend F xs S) ((Funi₁ , Funi₂) , Suni) =
      ((λ inc' → Funi₁ (⊆-trans inc inc')) ,
      (λ {Δ} {Ε} i₁ i₂ t →
      Begin[ Ε ⊩ σ ]
        Ε ⊩ σ ∋ ⊩-weaken σ i₁ (F (⊆-trans inc i₂) t)
        ≣⟨ Funi₂ i₁ (⊆-trans inc i₂) t ⟩
        Ε ⊩ σ ∋ F (⊆-trans (⊆-trans inc i₂) i₁) (ne-weaken i₁ t)
        ≡⟨ cong (λ pr → F pr (ne-weaken i₁ t)) (sym (⊆-assoc inc i₂ i₁)) ⟩
        Ε ⊩ σ ∋ F (⊆-trans inc (⊆-trans i₂ i₁)) (ne-weaken i₁ t)
      Qed)) ,
      Unilist-weaken σ inc S Suni

    Uni-weaken : ∀ {Γ Δ} σ (inc : Γ ⊆ Δ) {S : Γ ⊩ σ} (Suni : Uni[ σ ] S) →
      Uni[ σ ] ⊩-weaken σ inc S
    Uni-weaken `1 inc Suni = Suni
    Uni-weaken (σ `× τ) inc (Auni , Buni) = Uni-weaken σ inc Auni , Uni-weaken τ inc Buni
    Uni-weaken (σ `→ τ) inc {F} (h₁ , h₂ , h₃) =
      (λ inc' → h₁ (⊆-trans inc inc')) ,
      (λ inc' → h₂ (⊆-trans inc inc')) ,
      (λ {Ε} {Φ} i₁ i₂ S Suni →
      let S' : Φ ⊩ σ
          S' = ⊩-weaken σ i₁ S in
      Begin[ Φ ⊩ τ ]
        Φ ⊩ τ ∋ ⊩-weaken τ i₁ (F (⊆-trans inc i₂) S)
        ≣⟨ h₃ i₁ (⊆-trans inc i₂) S Suni ⟩
        Φ ⊩ τ ∋ F (⊆-trans (⊆-trans inc i₂) i₁) S'
        ≡⟨ cong (λ pr → F pr S') (sym (⊆-assoc inc i₂ i₁)) ⟩
        Φ ⊩ τ ∋ F (⊆-trans inc (⊆-trans i₂ i₁)) S'
      Qed)
    Uni-weaken (`list σ) inc {S} Suni = Unilist-weaken σ inc S Suni

abstract

  Uniε-weaken : ∀ {Δ Ε} Γ (inc : Δ ⊆ Ε) {R : Δ ⊩ε Γ} (Runi : Uni[ Γ ]ε R) →
      Uni[ Γ ]ε ⊩ε-weaken Γ inc R
  Uniε-weaken ε inc Runi = Runi
  Uniε-weaken (Γ ∙ σ) inc (Runi , runi) = Uniε-weaken Γ inc Runi , Uni-weaken σ inc runi

{- One can commute weakening and activation -}

abstract

  weaken-↓list : ∀ {Γ Δ} σ (inc : Γ ⊆ Δ) (t : Γ ⊢ne `list σ) →
    [ `list σ ] ⊩-weaken (`list σ) inc (↓[ `list σ ] t) ≣ ↓[ `list σ ] ne-weaken inc t
  weaken-↓list σ inc t = mappend (λ _ t → ≣-refl σ (↓[ σ ] t)) refl (≣-refl (`list σ) `[])

  weaken-↓ : ∀ {Γ Δ} σ (inc : Γ ⊆ Δ) (t : Γ ⊢ne σ) →
    [ σ ] ⊩-weaken σ inc (↓[ σ ] t) ≣ ↓[ σ ] ne-weaken inc t
  weaken-↓ `1 inc t = tt
  weaken-↓ (σ `× τ) inc t = weaken-↓ σ inc (`π₁ t) , weaken-↓ τ inc (`π₂ t)
  weaken-↓ (σ `→ τ) inc t =
    λ {Ε} inc' S Suni →
    Begin[ Ε ⊩ τ ]
      Ε ⊩ τ ∋ ↓[ τ ] (ne-weaken (⊆-trans inc inc') t `$ (↑[ σ ] S))
      ≡⟨ cong (λ t → ↓[ τ ] (t `$ (↑[ σ ] S))) (sym (ne-weaken² inc inc' t)) ⟩
      Ε ⊩ τ ∋ ↓[ τ ] (ne-weaken inc' (ne-weaken inc t) `$ (↑[ σ ] S))
    Qed
  weaken-↓ (`list σ) inc t = weaken-↓list σ inc t

{- ⊩ε-purge is compatible with uniformity -}

abstract

  Uniε-purge : ∀ {Γ Δ} (inc : Γ ⊆ Δ) {Ε} {R : Ε ⊩ε Δ} (Runi : Uni[ Δ ]ε R) →
    Uni[ Γ ]ε (⊩ε-purge inc R)
  Uniε-purge base Runi = Runi
  Uniε-purge (step inc) (Runi , runi) = Uniε-purge inc Runi
  Uniε-purge (pop! inc) (Runi , runi) = Uniε-purge inc Runi , runi

abstract

  Uni-lookup : ∀ {Γ Δ σ} (pr : σ ∈ Γ) {R : Δ ⊩ε Γ} (Runi : Uni[ Γ ]ε R) → Uni[ σ ] (lookup Γ pr R)
  Uni-lookup here! (_ , runi) = runi
  Uni-lookup (there pr) (Runi , _) = Uni-lookup pr Runi

  ≣-lookup : ∀ {Γ Δ σ} (pr : σ ∈ Γ) {R₁ : Δ ⊩ε Γ} {R₂ : Δ ⊩ε Γ}
    (eqR₁R₂ : [ Γ ] R₁ ≣ε R₂) → [ σ ] lookup Γ pr R₁ ≣ lookup Γ pr R₂
  ≣-lookup here! (_ , eqr₁r₂) = eqr₁r₂
  ≣-lookup (there pr) (eqR₁R₂ , _) = ≣-lookup pr eqR₁R₂

  weaken-lookup : ∀ {σ Γ Δ Ε} (inc : Δ ⊆ Ε) (pr : σ ∈ Γ) (R : Δ ⊩ε Γ) →
    [ σ ] ⊩-weaken σ inc (lookup Γ pr R) ≣ lookup Γ pr (⊩ε-weaken Γ inc R)
  weaken-lookup {σ} inc here! (_ , r) = ≣-refl σ _
  weaken-lookup inc (there pr) (R , _) = weaken-lookup inc pr R

mutual

  abstract

    Uni-ne : ∀ σ {Γ} (t : Γ ⊢ne σ) → Uni[ σ ] ↓[ σ ] t
    Uni-ne `1 t = tt
    Uni-ne (σ `× τ) t = Uni-ne σ (`π₁ t) , Uni-ne τ (`π₂ t)
    Uni-ne (σ `→ τ) t =
      (λ inc S Suni → Uni-ne τ (ne-weaken inc t `$ (↑[ σ ] S))) ,
      (λ {Δ} inc {S₁} {S₂} Suni₁ Suni₂ eqS₁S₂ →
      Begin[ Δ ⊩ τ ]
        Δ ⊩ τ ∋ ↓[ τ ] (ne-weaken inc t `$ (↑[ σ ] S₁))
        ≡⟨ cong (λ s → ↓[ τ ] (ne-weaken inc t `$ s)) (≣≡nf σ eqS₁S₂) ⟩
        Δ ⊩ τ ∋ ↓[ τ ] (ne-weaken inc t `$ (↑[ σ ] S₂))
      Qed) ,
      (λ {Δ} {Ε} i₁ i₂ S Suni → 
      Begin[ Ε ⊩ τ ] 
        Ε ⊩ τ ∋ ⊩-weaken τ i₁ (↓[ τ ] (ne-weaken i₂ t `$ (↑[ σ ] S)))
        ≣⟨ weaken-↓ τ i₁ (ne-weaken i₂ t `$ (↑[ σ ] S)) ⟩
        Ε ⊩ τ ∋ ↓[ τ ] (ne-weaken i₁ (ne-weaken i₂ t) `$ nf-weaken i₁ (↑[ σ ] S))
        ≡⟨ cong₂ (λ t' s' → ↓[ τ ] (t' `$ s')) (ne-weaken² i₂ i₁ t) (sym (weaken-↑ σ i₁ Suni)) ⟩
        Ε ⊩ τ ∋ ↓[ τ ] (ne-weaken (⊆-trans i₂ i₁) t `$ (↑[ σ ] ⊩-weaken σ i₁ S))
      Qed)
    Uni-ne (`list σ) t =
      ((λ inc t' → Uni-ne σ t') ,
      (λ i₁ i₂ t' → weaken-↓ σ i₁ t')) ,
      tt

    ≣list≡nf : ∀ {Γ} σ {S T : Γ ⊩ `list σ} (eq : [ `list σ ] S ≣ T) →
      ↑[ `list σ ] S ≡ ↑[ `list σ ] T
    ≣list≡nf σ `[] = refl
    ≣list≡nf σ (hd `∷ tl) = cong₂ _`∷_ (≣≡nf σ hd) (≣list≡nf σ tl)
    ≣list≡nf σ (mappend F xs YS) =
      cong₃ (λ f xs ys → mappend (`λ f) xs ys)
        (≣≡nf σ (F (step (same _)) (`v here!)))
        xs
        (≣list≡nf σ YS)

    ≣≡nf : ∀ {Γ} σ {S T : Γ ⊩ σ} (eq : [ σ ] S ≣ T) → ↑[ σ ] S ≡ ↑[ σ ] T
    ≣≡nf `1 eq = refl
    ≣≡nf (σ `× τ) (Aeq , Beq) = cong₂ _`,_ (≣≡nf σ Aeq) (≣≡nf τ Beq)
    ≣≡nf (σ `→ τ) eq = cong `λ (≣≡nf τ (eq (step (same _)) (↓[ σ ] `v here!) (Uni-ne σ (`v here!))))
    ≣≡nf (`list σ) eq = ≣list≡nf σ eq

    weaken-↑list : ∀ σ {Γ Δ} (inc : Γ ⊆ Δ) (S : Γ ⊩ `list σ) (Suni : Uni[ `list σ ] S) →
      ↑[ `list σ ] (⊩-weaken (`list σ) inc S) ≡ nf-weaken inc (↑[ `list σ ] S)
    weaken-↑list σ inc `[] Suni = refl
    weaken-↑list σ inc (HD `∷ TL) (HDuni , TLuni) =
      cong₂ _`∷_ (weaken-↑ σ inc HDuni) (weaken-↑list σ inc TL TLuni)
    weaken-↑list σ {Γ} {Δ} inc (mappend {τ} F xs YS) ((Funi₁ , Funi₂) , YSuni) =
      cong₂ (λ f ys → mappend (`λ f) (ne-weaken inc xs) ys)
      (trans (≣≡nf σ
        (Begin[ Δ ∙ τ ⊩ σ ]
           Δ ∙ τ ⊩ σ ∋ F (⊆-trans inc (step (⊆-refl Δ))) (`v here!)
           ≡⟨ cong (λ pr → F pr (`v here!)) (sym (⊆-step-same inc)) ⟩
           Δ ∙ τ ⊩ σ ∋ F (step (⊆-trans (⊆-refl Γ) inc)) (`v here!)
           ≣⟨ ≣-sym σ (Funi₂ (pop! inc) (step (same Γ)) (`v here!)) ⟩
           Δ ∙ τ ⊩ σ ∋ ⊩-weaken σ (pop! inc) (F (step (same Γ)) (`v here!))
        Qed))
        (weaken-↑ σ (pop! inc) (Funi₁ (step (same _)) (`v here!))))
      (weaken-↑list σ inc YS YSuni)

    weaken-↑ : ∀ σ {Γ Δ} (inc : Γ ⊆ Δ) {S : Γ ⊩ σ} (Suni : Uni[ σ ] S) →
      ↑[ σ ] (⊩-weaken σ inc S) ≡ nf-weaken inc (↑[ σ ] S)
    weaken-↑ `1 inc Suni = refl
    weaken-↑ (σ `× τ) inc (Auni , Buni) = cong₂ _`,_ (weaken-↑ σ inc Auni) (weaken-↑ τ inc Buni)
    weaken-↑ (σ `→ τ) {Γ} {Δ} inc {S} (h₁ , h₂ , h₃) =
      cong `λ
      (trans (≣≡nf τ (
        Begin[ Δ ∙ σ ⊩ τ ]
          Δ ∙ σ ⊩ τ ∋ S (⊆-trans inc (step (⊆-refl Δ))) (↓[ σ ] `v here!)
          ≡⟨ cong (λ pr → S pr (↓[ σ ] `v here!)) (sym (⊆-step-same inc)) ⟩
          Δ ∙ σ ⊩ τ ∋ S (step (⊆-trans (⊆-refl Γ) inc)) (↓[ σ ] `v here!)
          ≣⟨ h₂ (step (⊆-trans (⊆-refl Γ) inc)) (Uni-ne σ (`v here!))
             (Uni-weaken σ (pop! inc) (Uni-ne σ (`v here!)))
             (≣-sym σ (weaken-↓ σ (pop! inc) (`v here!))) ⟩
          Δ ∙ σ ⊩ τ ∋ S (step (⊆-trans (⊆-refl Γ) inc)) (⊩-weaken σ (pop! inc) (↓[ σ ] `v here!))
          ≣⟨ ≣-sym τ (h₃ (pop! inc) (step (same Γ)) (↓[ σ ] `v here!) (Uni-ne σ (`v here!))) ⟩
          Δ ∙ σ ⊩ τ ∋ ⊩-weaken τ (pop! inc) (S (step (same Γ)) (↓[ σ ] `v here!))
        Qed))
      (weaken-↑ τ (pop! inc) (h₁ (step (same _)) (↓[ σ ] `v here!) (Uni-ne σ (`v here!)))))
    weaken-↑ (`list σ) inc {S} Suni = weaken-↑list σ inc S Suni

abstract

  Uni-⊩ε-refl : ∀ Γ → Uni[ Γ ]ε ⊩ε-refl Γ
  Uni-⊩ε-refl ε = tt
  Uni-⊩ε-refl (Γ ∙ σ) = Uniε-weaken Γ (step (same Γ)) (Uni-⊩ε-refl Γ) , Uni-ne σ (`v here!)

mutual

  abstract

{- evaluation in uniform environments produces uniform values -}

    Uni-vappend : ∀ {Γ} σ (XS : Γ ⊩ `list σ) {YS : Γ ⊩ `list σ} (XSuni : Uni[ `list σ ] XS)
      (YSuni : Uni[ `list σ ] YS) → Uni[ `list σ ] vappend σ XS YS
    Uni-vappend σ `[] XSuni YSuni = YSuni
    Uni-vappend σ (HD `∷ XS) (HDuni , XSuni) YSuni = HDuni , Uni-vappend σ XS XSuni YSuni
    Uni-vappend σ (mappend F xs YS) (Funi , YSuni) ZSuni =
      Funi , Uni-vappend σ YS YSuni ZSuni

    Uni-vmap : ∀ {Γ} σ {τ} {F : Γ ⊩ σ `→ τ} (Funi : Uni[ σ `→ τ ] F)
      (XS : Γ ⊩ `list σ) (XSuni : Uni[ `list σ ] XS) → Uni[ `list τ ] vmap σ τ F XS
    Uni-vmap σ Funi `[] XSuni = XSuni
    Uni-vmap σ (h₁ , h₂ , h₃) (HD `∷ TL) (HDuni , TLuni) =
      h₁ (same _) HD HDuni , Uni-vmap σ (h₁ , h₂ , h₃) TL TLuni
    Uni-vmap {Γ} σ {τ} {F} (h₁ , h₂ , h₃) (mappend G xs YS) ((Guni₁ , Guni₂) , YSuni) =
      ((λ inc t → h₁ inc (G inc t) (Guni₁ inc t)) ,
      (λ {Δ} {Ε} i₁ i₂ t →
        Begin[ Ε ⊩ τ ]
          Ε ⊩ τ ∋ ⊩-weaken τ i₁ (F i₂ (G i₂ t))
          ≣⟨ h₃ i₁ i₂ (G i₂ t) (Guni₁ i₂ t) ⟩
          Ε ⊩ τ ∋ F (⊆-trans i₂ i₁) (⊩-weaken σ i₁ (G i₂ t))
          ≣⟨ h₂ (⊆-trans i₂ i₁) (Uni-weaken σ i₁ (Guni₁ i₂ t))
             (Guni₁ (⊆-trans i₂ i₁) (ne-weaken i₁ t)) (Guni₂ i₁ i₂ t) ⟩
          Ε ⊩ τ ∋ F (⊆-trans i₂ i₁) (G (⊆-trans i₂ i₁) (ne-weaken i₁ t))
        Qed)) ,
      Uni-vmap σ (h₁ , h₂ , h₃) YS YSuni

    Uni-vfold : ∀ {Γ} σ τ {C : Γ ⊩ σ `→ τ `→ τ} (Cuni : Uni[ σ `→ τ `→ τ ] C)
      {N : Γ ⊩ τ} (Nuni : Uni[ τ ] N) (XS : Γ ⊩ `list σ) (XSuni : Uni[ `list σ ] XS) →
      Uni[ τ ] vfold σ τ C N XS
    Uni-vfold σ τ Cuni Nuni `[] XSuni = Nuni
    Uni-vfold {Γ} σ τ {C} (h₁ , h₂ , h₃) {N} Nuni (HD `∷ TL) (HDuni , TLuni) =
      proj₁ (h₁ (same Γ) HD HDuni) (same _) (vfold σ τ C N TL)
      (Uni-vfold σ τ (h₁ , h₂ , h₃) Nuni TL TLuni)
    Uni-vfold {Γ} σ τ {C} Cuni {N} Nuni (mappend F xs YS) XSuni =
      Uni-ne τ (`fold (`λ (`λ (↑[ τ ] C (step (step (⊆-refl Γ)))
        (F (step (step (⊆-refl Γ))) (`v (there here!)))
        (pop! (pop! (⊆-refl Γ))) (↓[ τ ] `v here!)))) (↑[ τ ] vfold σ τ C N YS) xs)

    Uni-eval : ∀ {σ Γ Δ} (t : Γ ⊢ σ) {R : Δ ⊩ε Γ} (Runi : Uni[ Γ ]ε R) → Uni[ σ ] (eval t R)
    Uni-eval (`v pr) Runi = Uni-lookup pr Runi
    Uni-eval {σ `→ τ} {Γ} {Δ} (`λ t) {R} Runi =
      (λ inc S Suni → Uni-eval t (Uniε-weaken Γ inc Runi , Suni)) ,
      (λ inc Suni₁ Suni₂ eqS₁S₂ →
         let Runi' = Uniε-weaken Γ inc Runi in
         ≣-eval t (Runi' , Suni₁) (Runi' , Suni₂) (≣ε-refl Γ _ , eqS₁S₂)) ,
      (λ {Ε} {Φ} i₁ i₂ S Suni →
      let Runi-i₂ = Uniε-weaken Γ i₂ Runi
          Runi-i₁-i₂ = Uniε-weaken Γ i₁ Runi-i₂
          Runi-i₁i₂ = Uniε-weaken Γ (⊆-trans i₂ i₁) Runi
          Suni-i₁ = Uni-weaken σ i₁ Suni in
      Begin[ Φ ⊩ τ ]
        Φ ⊩ τ ∋ ⊩-weaken τ i₁ (eval t (⊩ε-weaken Γ i₂ R , S))
        ≣⟨ weaken-eval i₁ t (Runi-i₂ , Suni) ⟩
        Φ ⊩ τ ∋ eval t (⊩ε-weaken Γ i₁ (⊩ε-weaken Γ i₂ R) , ⊩-weaken σ i₁ S)
        ≣⟨ ≣-eval t (Runi-i₁-i₂ , Suni-i₁) (Runi-i₁i₂ , Suni-i₁)
           (≣ε-weaken² Γ i₂ i₁ R , ≣-refl σ (⊩-weaken σ i₁ S)) ⟩
        Φ ⊩ τ ∋ eval t (⊩ε-weaken Γ (⊆-trans i₂ i₁) R , ⊩-weaken σ i₁ S)
      Qed)
    Uni-eval (t `$ u) Runi with Uni-eval t Runi
    ... | h₁ , h₂ , h₃ = h₁ (same _) _ (Uni-eval u Runi)
    Uni-eval `⟨⟩ Runi = tt
    Uni-eval (a `, b) Runi = Uni-eval a Runi , Uni-eval b Runi
    Uni-eval (`π₁ p) Runi = proj₁ (Uni-eval p Runi)
    Uni-eval (`π₂ p) Runi = proj₂ (Uni-eval p Runi)
    Uni-eval `[] Runi = tt
    Uni-eval (hd `∷ tl) Runi = Uni-eval hd Runi , Uni-eval tl Runi
    Uni-eval {`list σ} (xs `++ ys) {R} Runi =
      Uni-vappend σ (eval xs R) (Uni-eval xs Runi) (Uni-eval ys Runi)
    Uni-eval (`map {σ} f xs) {R} Runi = Uni-vmap σ (Uni-eval f Runi) (eval xs R) (Uni-eval xs Runi)
    Uni-eval (`fold {σ} {τ} c n xs) {R} Runi =
      Uni-vfold σ τ (Uni-eval c Runi) (Uni-eval n Runi) (eval xs R) (Uni-eval xs Runi)


{- evaluation in semantically equivalent environments produces
   semantically equivalent values -}

    ≣-vappend : ∀ {Γ} σ {XS₁ XS₂ : Γ ⊩ `list σ} (eqXS₁XS₂ : [ `list σ ] XS₁ ≣ XS₂)
      {YS₁ YS₂ : Γ ⊩ `list σ} (eqYS₁YS₂ : [ `list σ ] YS₁ ≣ YS₂) →
      [ `list σ ] vappend σ XS₁ YS₁ ≣ vappend σ XS₂ YS₂
    ≣-vappend σ `[] eqYS₁YS₂ = eqYS₁YS₂
    ≣-vappend σ (hd `∷ tl) eqYS₁YS₂ = hd `∷ ≣-vappend σ tl eqYS₁YS₂
    ≣-vappend σ (mappend F xs eqXS₁XS₂) eqYS₁YS₂ = mappend F xs (≣-vappend σ eqXS₁XS₂ eqYS₁YS₂)

    ≣-vmap : ∀ {Γ} σ τ {F₁ F₂ : Γ ⊩ σ `→ τ} (Funi₁ : Uni[ σ `→ τ ] F₁)
      (eqF₁F₂ : [ σ `→ τ ] F₁ ≣ F₂) {XS₁ XS₂ : Γ ⊩ `list σ} (XSuni₁ : Uni[ `list σ ] XS₁)
      (XSuni₂ : Uni[ `list σ ] XS₂) (eqXS₁XS₂ : [ `list σ ] XS₁ ≣ XS₂) →
      [ `list τ ] vmap σ τ F₁ XS₁ ≣ vmap σ τ F₂ XS₂
    ≣-vmap σ τ Funi₁ eqF₁F₂ XSuni₁ XSuni₂ `[] = `[]
    ≣-vmap {Γ} σ τ {F₁} {F₂} (h₁ , h₂ , h₃) eqF₁F₂ {X₁ `∷ XS₁} {X₂ `∷ XS₂}
      (Xuni₁ , XSuni₁) (Xuni₂ , XSuni₂) (hd `∷ tl) =
      (Begin[ Γ ⊩ τ ]
        Γ ⊩ τ ∋ F₁ (⊆-refl Γ) X₁
        ≣⟨ h₂ (same Γ) Xuni₁ Xuni₂ hd ⟩
        Γ ⊩ τ ∋ F₁ (⊆-refl Γ) X₂
        ≣⟨ eqF₁F₂ (same Γ) X₂ Xuni₂ ⟩
        Γ ⊩ τ ∋ F₂ (⊆-refl Γ) X₂
      Qed)
      `∷ ≣-vmap σ τ (h₁ , h₂ , h₃) eqF₁F₂ XSuni₁ XSuni₂ tl
    ≣-vmap {Γ} σ τ {F₁} {F₂} (h₁ , h₂ , h₃) eqF₁F₂ {mappend G₁ xs₁ YS₁} {mappend G₂ xs₂ YS₂}
      (Guni₁ , YSuni₁) (Guni₂ , YSuni₂) (mappend G xs eqYS₁YS₂) =
      mappend (λ {Δ} inc t →
        Begin[ Δ ⊩ τ ]
          Δ ⊩ τ ∋ F₁ inc (G₁ inc t)
          ≣⟨ h₂ inc (proj₁ Guni₁ inc t) (proj₁ Guni₂ inc t) (G inc t) ⟩
          Δ ⊩ τ ∋ F₁ inc (G₂ inc t)
          ≣⟨ eqF₁F₂ inc (G₂ inc t) (proj₁ Guni₂ inc t) ⟩
          Δ ⊩ τ ∋ F₂ inc (G₂ inc t)
        Qed)
      xs (≣-vmap σ τ (h₁ , h₂ , h₃) eqF₁F₂ YSuni₁ YSuni₂ eqYS₁YS₂)

    ≣-vfold : ∀ {Γ} σ τ {C₁ C₂ : Γ ⊩ σ `→ τ `→ τ} (Cuni₁ : Uni[ σ `→ τ `→ τ ] C₁)
      (Cuni₂ : Uni[ σ `→ τ `→ τ ] C₂) (eqC₁C₂ : [ σ `→ τ `→ τ ] C₁ ≣ C₂) {N₁ N₂ : Γ ⊩ τ}
      (Nuni₁ : Uni[ τ ] N₁) (Nuni₂ : Uni[ τ ] N₂) (eqN₁N₂ : [ τ ] N₁ ≣ N₂)
      {XS₁ XS₂ : Γ ⊩ `list σ} (XSuni₁ : Uni[ `list σ ] XS₁) (XSuni₂ : Uni[ `list σ ] XS₂)
      (eqXS₁XS₂ : [ `list σ ] XS₁ ≣ XS₂) →
      [ τ ] vfold σ τ C₁ N₁ XS₁ ≣ vfold σ τ C₂ N₂ XS₂
    ≣-vfold σ τ Cuni₁ Cuni₂ eqC₁C₂ Nuni₁ Nuni₂ eqN₁N₂ XSuni₁ XSuni₂ `[] = eqN₁N₂
    ≣-vfold {Γ} σ τ {C₁} {C₂} (h₁ , h₂ , h₃) Cuni₂ eqC₁C₂ {N₁} {N₂} Nuni₁ Nuni₂ eqN₁N₂
      {X₁ `∷ XS₁} {X₂ `∷ XS₂} (Xuni₁ , XSuni₁) (Xuni₂ , XSuni₂) (hd `∷ tl) =
      let Uni-vfold₁ = Uni-vfold σ τ (h₁ , h₂ , h₃) Nuni₁ XS₁ XSuni₁
          Uni-vfold₂ = Uni-vfold σ τ Cuni₂ Nuni₂ XS₂ XSuni₂
          ind-hypo = ≣-vfold σ τ (h₁ , h₂ , h₃) Cuni₂ eqC₁C₂ Nuni₁ Nuni₂ eqN₁N₂ XSuni₁ XSuni₂ tl in
      Begin[ Γ ⊩ τ ]
        Γ ⊩ τ ∋ C₁ (same Γ) X₁ (same Γ) (vfold σ τ C₁ N₁ XS₁)
        ≣⟨ h₂ (same Γ) Xuni₁ Xuni₂ hd (same _) (vfold σ τ C₁ N₁ XS₁) Uni-vfold₁ ⟩
        Γ ⊩ τ ∋ C₁ (same Γ) X₂ (same Γ) (vfold σ τ C₁ N₁ XS₁)
        ≣⟨ proj₁ (proj₂ (h₁ (⊆-refl Γ) X₂ Xuni₂)) (same Γ) Uni-vfold₁ Uni-vfold₂ ind-hypo ⟩
        Γ ⊩ τ ∋ C₁ (same Γ) X₂ (same Γ) (vfold σ τ C₂ N₂ XS₂)
        ≣⟨ eqC₁C₂ (same Γ) X₂ Xuni₂ (same Γ) (vfold σ τ C₂ N₂ XS₂) Uni-vfold₂ ⟩
        Γ ⊩ τ ∋ C₂ (⊆-refl Γ) X₂ (⊆-refl Γ) (vfold σ τ C₂ N₂ XS₂)
      Qed 
    ≣-vfold {Γ} σ τ {C₁} {C₂} (h₁ , h₂ , h₃) Cuni₂ eqC₁C₂ {N₁} {N₂} Nuni₁ Nuni₂ eqN₁N₂
      {mappend F₁ xs YS₁} {mappend F₂ .xs YS₂} (Funi₁ , YSuni₁) (Funi₂ , YSuni₂) (mappend F refl YS) =
      let ind-hypo = ≣-vfold σ τ (h₁ , h₂ , h₃) Cuni₂ eqC₁C₂ Nuni₁ Nuni₂ eqN₁N₂ YSuni₁ YSuni₂ YS in
      Begin[ Γ ⊩ τ ]
        Γ ⊩ τ ∋ _
        ≡⟨ cong₂ (λ cf n → ↓[ τ ] `fold (`λ (`λ cf)) n xs)
          (≣≡nf τ
            (Begin[ Γ ∙ _ ∙ _ ⊩ τ ] 
               Γ ∙ _ ∙ _ ⊩ τ ∋ _
               ≣⟨ h₂ _ (proj₁ Funi₁ _ _) (proj₁ Funi₂ _ _) (F _ _) (same _) _ (Uni-ne τ (`v here!)) ⟩
               Γ ∙ _ ∙ _ ⊩ τ ∋ _
               ≣⟨ eqC₁C₂ _ _ (proj₁ Funi₂ _ _) (same _) _ (Uni-ne τ (`v here!)) ⟩
               Γ ∙ _ ∙ _ ⊩ τ ∋ _
             Qed))
          (≣≡nf τ ind-hypo) ⟩
        Γ ⊩ τ ∋ _
      Qed

    ≣-eval : ∀ {Γ Δ σ} (t : Γ ⊢ σ) {R₁ : Δ ⊩ε Γ} (Runi₁ : Uni[ Γ ]ε R₁)
      {R₂ : Δ ⊩ε Γ} (Runi₂ : Uni[ Γ ]ε R₂) (eqR₁R₂ : [ Γ ] R₁ ≣ε R₂) →
      [ σ ] eval t R₁ ≣ eval t R₂
    ≣-eval (`v pr) Runi₁ Runi₂ eqR₁R₂ = ≣-lookup pr eqR₁R₂
    ≣-eval {Γ} {Δ} {σ `→ τ} (`λ t) Runi₁ Runi₂ eqR₁R₂ =
      λ inc S Suni →
        ≣-eval t (Uniε-weaken Γ inc Runi₁ , Suni) (Uniε-weaken Γ inc Runi₂ , Suni)
        (≣ε-weaken Γ inc eqR₁R₂ , ≣-refl σ S)
    ≣-eval {Γ} {Δ} {τ} (t `$ u) {R₁} Runi₁ {R₂} Runi₂ eqR₁R₂ with Uni-eval t Runi₁
    ... | h₁ , h₂ , h₃ =
      Begin[ Δ ⊩ τ ]
        Δ ⊩ τ ∋ eval t R₁ (same Δ) (eval u R₁)
        ≣⟨ h₂ (same Δ) (Uni-eval u Runi₁) (Uni-eval u Runi₂) (≣-eval u Runi₁ Runi₂ eqR₁R₂) ⟩
        Δ ⊩ τ ∋ eval t R₁ (same Δ) (eval u R₂)
        ≣⟨ ≣-eval t Runi₁ Runi₂ eqR₁R₂ (same _) (eval u R₂) (Uni-eval u Runi₂) ⟩
        Δ ⊩ τ ∋ eval t R₂ (⊆-refl Δ) (eval u R₂)
      Qed
    ≣-eval `⟨⟩ Runi₁ Runi₂ eqR₁R₂ = tt
    ≣-eval (a `, b) Runi₁ Runi₂ eqR₁R₂ = ≣-eval a Runi₁ Runi₂ eqR₁R₂ , ≣-eval b Runi₁ Runi₂ eqR₁R₂
    ≣-eval (`π₁ p) Runi₁ Runi₂ eqR₁R₂ = proj₁ (≣-eval p Runi₁ Runi₂ eqR₁R₂)
    ≣-eval (`π₂ p) Runi₁ Runi₂ eqR₁R₂ = proj₂ (≣-eval p Runi₁ Runi₂ eqR₁R₂)
    ≣-eval `[] Runi₁ Runi₂ eqR₁R₂ = `[]
    ≣-eval (hd `∷ tl) Runi₁ Runi₂ eqR₁R₂ =
      (≣-eval hd Runi₁ Runi₂ eqR₁R₂) `∷ (≣-eval tl Runi₁ Runi₂ eqR₁R₂)
    ≣-eval {σ = `list σ} (xs `++ ys) Runi₁ Runi₂ eqR₁R₂ =
      ≣-vappend σ (≣-eval xs Runi₁ Runi₂ eqR₁R₂) (≣-eval ys Runi₁ Runi₂ eqR₁R₂)
    ≣-eval (`map {σ} {τ} f xs) Runi₁ Runi₂ eqR₁R₂ =
      ≣-vmap σ τ (Uni-eval f Runi₁) (≣-eval f Runi₁ Runi₂ eqR₁R₂)
      (Uni-eval xs Runi₁) (Uni-eval xs Runi₂) (≣-eval xs Runi₁ Runi₂ eqR₁R₂)
    ≣-eval (`fold {σ} {τ} c n xs) Runi₁ Runi₂ eqR₁R₂ =
     ≣-vfold σ τ (Uni-eval c Runi₁) (Uni-eval c Runi₂) (≣-eval c Runi₁ Runi₂ eqR₁R₂)
     (Uni-eval n Runi₁) (Uni-eval n Runi₂) (≣-eval n Runi₁ Runi₂ eqR₁R₂)
     (Uni-eval xs Runi₁) (Uni-eval xs Runi₂) (≣-eval xs Runi₁ Runi₂ eqR₁R₂)

    weaken-vappend : ∀ σ {Γ Δ} (inc : Γ ⊆ Δ) (XS YS : Γ ⊩ `list σ) →
      [ `list σ ] ⊩-weaken (`list σ) inc (vappend σ XS YS) ≣
      vappend σ (⊩-weaken (`list σ) inc XS) (⊩-weaken (`list σ) inc YS)
    weaken-vappend σ inc `[] YS = ≣-refl (`list σ) _
    weaken-vappend σ inc (HD `∷ TL) YS = (≣-refl σ _) `∷ (weaken-vappend σ inc TL YS)
    weaken-vappend σ inc (mappend F xs XS) YS =
     mappend (λ _ _ → ≣-refl σ _) refl (weaken-vappend σ inc XS YS)

    weaken-vmap : ∀ σ τ {Γ Δ} (inc : Γ ⊆ Δ) {F : Γ ⊩ σ `→ τ} (Funi : Uni[ σ `→ τ ] F)
      (XS : Γ ⊩ `list σ) (XSuni : Uni[ `list σ ] XS) →
      [ `list τ ] ⊩-weaken (`list τ) inc (vmap σ τ F XS) ≣
      vmap σ τ (⊩-weaken (σ `→ τ) inc F) (⊩-weaken (`list σ) inc XS)
    weaken-vmap σ τ inc Funi `[] XSuni = `[]
    weaken-vmap σ τ {Γ} {Δ} inc {F} (h₁ , h₂ , h₃) (HD `∷ TL) (HDuni , TLuni) =
      (Begin[ Δ ⊩ τ ]
         Δ ⊩ τ ∋ ⊩-weaken τ inc (F (⊆-refl Γ) HD)
         ≣⟨ h₃ inc (same Γ) HD HDuni ⟩
         Δ ⊩ τ ∋ F (⊆-trans (same Γ) inc) (⊩-weaken σ inc HD)
         ≡⟨ cong (λ pr → F pr (⊩-weaken σ inc HD)) (sym (⊆-same-swap inc)) ⟩
         Δ ⊩ τ ∋ F (⊆-trans inc (same Δ)) (⊩-weaken σ inc HD)
       Qed)
       `∷ weaken-vmap σ τ inc (h₁ , h₂ , h₃) TL TLuni
    weaken-vmap σ τ inc {F} Funi (mappend G xs YS) (Guni , YSuni) =
      mappend (λ _ _ → ≣-refl τ _) refl (weaken-vmap σ τ inc Funi YS YSuni)

    weaken-vfold : ∀ σ τ {Γ Δ} (inc : Γ ⊆ Δ) {C : Γ ⊩ σ `→ τ `→ τ} (Cuni : Uni[ σ `→ τ `→ τ ] C)
      {N : Γ ⊩ τ} (Nuni : Uni[ τ ] N) (XS : Γ ⊩ `list σ) (XSuni : Uni[ `list σ ] XS) →
      [ τ ] ⊩-weaken τ inc (vfold σ τ C N XS) ≣
      vfold σ τ (⊩-weaken (σ `→ τ `→ τ) inc C) (⊩-weaken τ inc N) (⊩-weaken (`list σ) inc XS)
    weaken-vfold σ τ inc Cuni Nuni `[] XSuni = ≣-refl τ _
    weaken-vfold σ τ {Γ} {Δ} inc {C} (h₁ , h₂ , h₃) {N} Nuni (HD `∷ TL) (HDuni , TLuni) =
      let Cuni' = Uni-weaken (σ `→ τ `→ τ) inc (h₁ , h₂ , h₃)
          Nuni' = Uni-weaken τ inc Nuni
          TLuni' = Uni-weaken (`list σ) inc {TL} TLuni in
      Begin[ Δ ⊩ τ ]
        Δ ⊩ τ ∋ ⊩-weaken τ inc (C (same Γ) HD (same Γ) (vfold σ τ C N TL))
        ≣⟨ proj₂ (proj₂ (h₁ (⊆-refl Γ) HD HDuni)) inc (same Γ) (vfold σ τ C N TL)
           (Uni-vfold σ τ (h₁ , h₂ , h₃) Nuni TL TLuni) ⟩
        Δ ⊩ τ ∋ _
        ≡⟨ cong (λ pr → C (same Γ) HD pr (⊩-weaken τ inc (vfold σ τ C N TL)))
           (sym (⊆-same-swap inc)) ⟩
        Δ ⊩ τ ∋ _
        ≣⟨ proj₁ (proj₂ (h₁ (⊆-refl Γ) HD HDuni)) (⊆-trans inc (same Δ))
           (Uni-weaken τ inc (Uni-vfold σ τ (h₁ , h₂ , h₃) Nuni TL TLuni))
           (Uni-vfold σ τ Cuni' Nuni' (⊩-weaken (`list σ) inc TL) TLuni')
           (weaken-vfold σ τ inc (h₁ , h₂ , h₃) Nuni TL TLuni) ⟩
        Δ ⊩ τ ∋ _
        ≣⟨ h₃ inc (same Γ) HD HDuni (same Δ) _
           (Uni-vfold σ τ Cuni' Nuni' (⊩-weaken (`list σ) inc TL) TLuni') ⟩
        Δ ⊩ τ ∋ _
        ≡⟨ cong (λ pr → C pr (⊩-weaken σ inc HD) (same Δ)
          (vfold σ τ (⊩-weaken (σ `→ τ `→ τ) inc C) (⊩-weaken τ inc N)
          (⊩-weaken (`list σ) inc TL))) (sym (⊆-same-swap inc)) ⟩
        Δ ⊩ τ ∋ _
      Qed
    weaken-vfold σ τ {Γ} {Δ} inc {C} (h₁ , h₂ , h₃) {N} Nuni (mappend F xs YS)
      ((Funi₁ , Funi₂) , YSuni) =
      let vuni = Uni-ne τ (`v here!)
          vuni' = Uni-weaken τ (pop! (pop! inc)) vuni in
      Begin[ Δ ⊩ τ ]
        Δ ⊩ τ ∋ _
        ≣⟨ weaken-↓ τ inc _ ⟩
        Δ ⊩ τ ∋ _
        ≡⟨ cong₂ (λ cf nys → ↓[ τ ] `fold (`λ (`λ cf)) nys (ne-weaken inc xs))
           (sym (weaken-↑ τ (pop! (pop! inc)) (proj₁ (h₁ _ _ (Funi₁ _ _)) _ _ vuni)))
           (sym (weaken-↑ τ inc (Uni-vfold σ τ (h₁ , h₂ , h₃) Nuni YS YSuni))) ⟩
        Δ ⊩ τ ∋ _
        ≡⟨ cong₂ (λ cf nys → ↓[ τ ] `fold (`λ (`λ cf)) nys (ne-weaken inc xs))
           (≣≡nf τ (
           Begin[ _ ⊩ τ ]
             _ ⊩ τ ∋ _
             ≣⟨ proj₂ (proj₂ (h₁ _ _ (Funi₁ _ _))) _ _ _ vuni ⟩
             _ ⊩ τ ∋ _
             ≡⟨ cong (λ pr → C (step (step (same Γ))) (F (step (step (same Γ))) (`v (there here!)))
                 pr (⊩-weaken τ (pop! (pop! inc)) (↓[ τ ] `v here!)))
                 (sym (⊆-same-swap (pop! (pop! inc)))) ⟩
             _ ⊩ τ ∋ _
             ≣⟨ h₃ (pop! (pop! inc)) (step (step (same Γ))) _ (Funi₁ _ _) (same _) _ vuni' ⟩
             _ ⊩ τ ∋ _
             ≣⟨ h₂ _ (Uni-weaken σ _ (Funi₁ _ _)) (Funi₁ _ _) (Funi₂ _ _ _) _ _ vuni' ⟩
             _ ⊩ τ ∋ _
             ≣⟨ proj₁ (proj₂ (h₁ _ _ (Funi₁ _ _))) (same _) vuni' (Uni-ne τ (`v here!))
                (weaken-↓ τ (pop! (pop! inc)) (`v here!)) ⟩
             _ ⊩ τ ∋ _
             ≡⟨ cong (λ pr → C pr (F pr (`v (there here!))) (⊆-refl _) (↓[ τ ] `v here!))
                (⊆-step₂-same inc) ⟩
             _ ⊩ τ ∋ _
           Qed ))
           (≣≡nf τ (weaken-vfold σ τ inc (h₁ , h₂ , h₃) Nuni YS YSuni)) ⟩
        Δ ⊩ τ ∋ _
      Qed

 {- Weakening of the evaluation of a term is the evaluation of
    the same term in a weakened environment. -}

    weaken-eval : ∀ {Δ Ε} (inc : Δ ⊆ Ε) {Γ σ} (t : Γ ⊢ σ) {R : Δ ⊩ε Γ}
      (Runi : Uni[ Γ ]ε R) → [ σ ] ⊩-weaken σ inc (eval t R) ≣ eval t (⊩ε-weaken Γ inc R)
    weaken-eval inc (`v pr) {R} Runi = weaken-lookup inc pr R
    weaken-eval inc {Γ} {σ `→ τ} (`λ t) {R} Runi =
      λ inc' S Suni → ≣-eval t
        (Uniε-weaken Γ (⊆-trans inc inc') Runi , Suni)
        (Uniε-weaken Γ inc' (Uniε-weaken Γ inc Runi) , Suni)
        (≣ε-sym Γ (≣ε-weaken² Γ inc inc' R) , ≣-refl σ S)
    weaken-eval {Δ} {Ε} inc {Γ} {τ} (_`$_ {σ} t u) {R} Runi with Uni-eval t Runi
    ... | h₁ , h₂ , h₃ =
      Begin[ Ε ⊩ τ ]
        Ε ⊩ τ ∋ ⊩-weaken τ inc (eval t R (same Δ) (eval u R))
        ≣⟨ h₃ inc (same Δ) (eval u R) (Uni-eval u Runi) ⟩
        Ε ⊩ τ ∋ eval t R (⊆-trans (⊆-refl Δ) inc) (⊩-weaken σ inc (eval u R))
        ≣⟨ h₂ (⊆-trans (⊆-refl Δ) inc) (Uni-weaken σ inc (Uni-eval u Runi))
           (Uni-eval u (Uniε-weaken Γ inc Runi)) (weaken-eval inc u Runi) ⟩
        Ε ⊩ τ ∋ eval t R (⊆-trans (⊆-refl Δ) inc) (eval u (⊩ε-weaken Γ inc R))
        ≡⟨ cong (λ pr → eval t R pr (eval u (⊩ε-weaken Γ inc R))) (sym (⊆-same-swap inc)) ⟩
        Ε ⊩ τ ∋ eval t R (⊆-trans inc (⊆-refl Ε)) (eval u (⊩ε-weaken Γ inc R))
        ≣⟨ weaken-eval inc t Runi (same Ε) _ (Uni-eval u (Uniε-weaken Γ inc Runi)) ⟩
        Ε ⊩ τ ∋ eval t (⊩ε-weaken Γ inc R) (⊆-refl Ε) (eval u (⊩ε-weaken Γ inc R))
      Qed
    weaken-eval inc `⟨⟩ Runi = tt
    weaken-eval inc (a `, b) Runi = weaken-eval inc a Runi , weaken-eval inc b Runi
    weaken-eval inc (`π₁ p) Runi = proj₁ (weaken-eval inc p Runi)
    weaken-eval inc (`π₂ p) Runi = proj₂ (weaken-eval inc p Runi)
    weaken-eval inc `[] Runi = `[]
    weaken-eval inc (hd `∷ tl) Runi = weaken-eval inc hd Runi `∷ weaken-eval inc tl Runi
    weaken-eval {Δ} {Ε} inc {Γ} {`list σ} (xs `++ ys) {R} Runi =
      Begin[ Ε ⊩ `list σ ]
        Ε ⊩ `list σ ∋ _
        ≣⟨ weaken-vappend σ inc (eval xs R) (eval ys R) ⟩
        Ε ⊩ `list σ ∋ _
        ≣⟨ ≣-vappend σ (weaken-eval inc xs Runi) (weaken-eval inc ys Runi) ⟩
        Ε ⊩ `list σ ∋ _
      Qed
    weaken-eval {Δ} {Ε} inc {Γ} (`map {σ} {τ} f xs) {R} Runi =
      Begin[ Ε ⊩ `list τ ]
        Ε ⊩ `list τ ∋ _
        ≣⟨ weaken-vmap σ τ inc (Uni-eval f Runi) (eval xs R) (Uni-eval xs Runi) ⟩
        Ε ⊩ `list τ ∋ _
        ≣⟨ ≣-vmap σ τ (Uni-weaken (σ `→ τ) inc (Uni-eval f Runi)) (weaken-eval inc f Runi)
           (Uni-weaken (`list σ) inc {eval xs R} (Uni-eval xs Runi))
           (Uni-eval xs (Uniε-weaken Γ inc Runi)) (weaken-eval inc xs Runi) ⟩
        Ε ⊩ `list τ ∋ _
      Qed
    weaken-eval {Δ} {Ε} inc {Γ} (`fold {σ} {τ} c n xs) {R} Runi =
      let Runi' = Uniε-weaken Γ inc Runi in
      Begin[ Ε ⊩ τ ]
        Ε ⊩ τ ∋ ⊩-weaken τ inc (eval (`fold c n xs) R)
        ≣⟨ weaken-vfold σ τ inc (Uni-eval c Runi) (Uni-eval n Runi) (eval xs R) (Uni-eval xs Runi) ⟩
        Ε ⊩ τ ∋ _
        ≣⟨ ≣-vfold σ τ (Uni-weaken (σ `→ τ `→ τ) inc (Uni-eval c Runi)) (Uni-eval c Runi')
           (weaken-eval inc c Runi) (Uni-weaken τ inc (Uni-eval n Runi)) (Uni-eval n Runi')
           (weaken-eval inc n Runi) (Uni-weaken (`list σ) inc {eval xs R} (Uni-eval xs Runi))
           (Uni-eval xs Runi') (weaken-eval inc xs Runi) ⟩
        Ε ⊩ τ ∋ _
      Qed

abstract

  Uniε-eval : ∀ {Δ Ε} Γ (γ : Δ ⊢ε Γ) {R : Ε ⊩ε Δ} (Runi : Uni[ Δ ]ε R) → Uni[ Γ ]ε (εeval Γ γ R)
  Uniε-eval ε γ Runi = γ
  Uniε-eval (Γ ∙ σ) (γ , g) Runi = Uniε-eval Γ γ Runi , Uni-eval g Runi

  ≣ε-eval : ∀ {Δ Ε} Γ (γ : Δ ⊢ε Γ) {R₁ R₂ : Ε ⊩ε Δ} (Runi₁ : Uni[ Δ ]ε R₁) (Runi₂ : Uni[ Δ ]ε R₂)
    (eqR₁R₂ : [ Δ ] R₁ ≣ε R₂) → [ Γ ] εeval Γ γ R₁ ≣ε εeval Γ γ R₂
  ≣ε-eval ε γ Runi₁ Runi₂ eqR₁R₂ = tt
  ≣ε-eval (Γ ∙ σ) (γ , g) Runi₁ Runi₂ eqR₁R₂ =
    ≣ε-eval Γ γ Runi₁ Runi₂ eqR₁R₂ , ≣-eval g Runi₁ Runi₂ eqR₁R₂

  weaken-εeval : ∀ Γ {Ε Φ} (inc : Ε ⊆ Φ) {Δ} (γ : Δ ⊢ε Γ) {R : Ε ⊩ε Δ} (Runi : Uni[ Δ ]ε R) →
    [ Γ ] ⊩ε-weaken Γ inc (εeval Γ γ R) ≣ε εeval Γ γ (⊩ε-weaken Δ inc R)
  weaken-εeval ε inc γ Runi = tt
  weaken-εeval (Γ ∙ σ) inc (γ , g) Runi = weaken-εeval Γ inc γ Runi , weaken-eval inc g Runi

≡-to-≣ε : ∀ Γ {Δ} {R₁ R₂ : Δ ⊩ε Γ} (eq : R₁ ≡ R₂) → [ Γ ] R₁ ≣ε R₂
≡-to-≣ε Γ refl = ≣ε-refl Γ _

abstract

  lookup-weaken : ∀ {σ Γ} (pr : σ ∈ Γ) {Δ} (inc : Γ ⊆ Δ) {Ε} (R : Ε ⊩ε Δ) →
    [ σ ] lookup Δ (inc-in inc pr) R ≣ lookup Γ pr (⊩ε-purge inc R)
  lookup-weaken () base R
  lookup-weaken pr (step inc) (R , _) = lookup-weaken pr inc R
  lookup-weaken {σ} here! (pop! inc) (_ , r) = ≣-refl σ r
  lookup-weaken (there pr) (pop! inc) (R , _) = lookup-weaken pr inc R

  eval-weaken : ∀ {Γ σ} (t : Γ ⊢ σ) {Δ} (inc : Γ ⊆ Δ) {Ε} {R : Ε ⊩ε Δ} (Runi : Uni[ Δ ]ε R) →
    [ σ ] eval (⊢-weaken inc t) R ≣ eval t (⊩ε-purge inc R)
  eval-weaken (`v pr) inc {Ε} {R} Runi = lookup-weaken pr inc R
  eval-weaken {Γ} (`λ {σ} {τ} t) {Δ} inc {Ε} {R} Runi =
    λ {Φ} inc' S Suni →
    let Runi' = Uniε-weaken Δ inc' Runi in
    Begin[ Φ ⊩ τ ]
      Φ ⊩ τ ∋ eval (⊢-weaken (pop! inc) t) (⊩ε-weaken Δ inc' R , S)
      ≣⟨ eval-weaken t (pop! inc) (Runi' , Suni) ⟩
      Φ ⊩ τ ∋ eval t (⊩ε-purge inc (⊩ε-weaken Δ inc' R) , S)
      ≣⟨ ≣-eval t (Uniε-purge inc Runi' , Suni)
         (Uniε-weaken Γ inc' (Uniε-purge inc Runi) , Suni)
         (≡-to-≣ε Γ (⊩ε-purge-weaken inc inc' R) , ≣-refl σ S) ⟩
      Φ ⊩ τ ∋ eval t (⊩ε-weaken Γ inc' (⊩ε-purge inc R) , S)
    Qed
  eval-weaken {σ = τ} (t `$ u) inc {Ε} {R} Runi with Uni-eval (⊢-weaken inc t) Runi
  ... | h₁ , h₂ , h₃ =
    let Runi' = Uniε-purge inc Runi in
    let Uuni = Uni-eval u Runi' in
    Begin[ Ε ⊩ τ ]
      Ε ⊩ τ ∋ eval (⊢-weaken inc t) R (same Ε) (eval (⊢-weaken inc u) R)
      ≣⟨ h₂ (same Ε) (Uni-eval (⊢-weaken inc u) Runi) Uuni (eval-weaken u inc Runi) ⟩
      Ε ⊩ τ ∋ eval (⊢-weaken inc t) R (⊆-refl Ε) (eval u (⊩ε-purge inc R))
      ≣⟨ eval-weaken t inc Runi (same Ε) _ Uuni ⟩
      Ε ⊩ τ ∋ eval t (⊩ε-purge inc R) (⊆-refl Ε) (eval u (⊩ε-purge inc R))
    Qed
  eval-weaken `⟨⟩ inc Runi = tt
  eval-weaken (a `, b) inc Runi = eval-weaken a inc Runi , eval-weaken b inc Runi
  eval-weaken (`π₁ p) inc Runi = proj₁ (eval-weaken p inc Runi)
  eval-weaken (`π₂ p) inc Runi = proj₂ (eval-weaken p inc Runi)
  eval-weaken `[] inc Runi = `[]
  eval-weaken (hd `∷ tl) inc Runi = (eval-weaken hd inc Runi) `∷ (eval-weaken tl inc Runi)
  eval-weaken {σ = `list σ} (xs `++ ys) inc Runi =
    ≣-vappend σ (eval-weaken xs inc Runi) (eval-weaken ys inc Runi)
  eval-weaken (`map {σ} {τ} f xs) inc Runi =
    ≣-vmap σ τ (Uni-eval (⊢-weaken inc f) Runi) (eval-weaken f inc Runi)
    (Uni-eval (⊢-weaken inc xs) Runi) (Uni-eval xs (Uniε-purge inc Runi)) (eval-weaken xs inc Runi)
  eval-weaken (`fold {σ} {τ} c n xs) inc Runi =
    let Runi' = Uniε-purge inc Runi in
    ≣-vfold σ τ (Uni-eval (⊢-weaken inc c) Runi) (Uni-eval c Runi') (eval-weaken c inc Runi)
    (Uni-eval (⊢-weaken inc n) Runi) (Uni-eval n Runi') (eval-weaken n inc Runi)
    (Uni-eval (⊢-weaken inc xs) Runi) (Uni-eval xs Runi') (eval-weaken xs inc Runi)

  εeval-weaken : ∀ {Δ} Γ {γ : Δ ⊢ε Γ} {Ε} (inc : Δ ⊆ Ε) {Φ} {R : Φ ⊩ε Ε} (Runi : Uni[ Ε ]ε R) →
    [ Γ ] εeval Γ (⊢ε-weaken Γ inc γ) R ≣ε εeval Γ γ (⊩ε-purge inc R)
  εeval-weaken ε inc Runi = tt
  εeval-weaken (Γ ∙ σ) {γ , g} inc Runi = εeval-weaken Γ inc Runi , eval-weaken g inc Runi

  εeval-⊢ε-refl : ∀ {Δ} Γ {R : Δ ⊩ε Γ} (Runi : Uni[ Γ ]ε R) → [ Γ ] εeval Γ (⊢ε-refl Γ) R ≣ε R
  εeval-⊢ε-refl ε Runi = tt
  εeval-⊢ε-refl {Δ} (Γ ∙ σ) {R , r} (Runi , runi) =
    (Begin[ Δ ⊩ε Γ ]
       Δ ⊩ε Γ ∋ εeval Γ (⊢ε-weaken Γ (step (same Γ)) (⊢ε-refl Γ)) (R , r)
       ≣⟨ εeval-weaken Γ (step (same Γ)) (Runi , runi) ⟩
       Δ ⊩ε Γ ∋ εeval Γ (⊢ε-refl Γ) (⊩ε-purge (same Γ) R)
       ≣⟨ ≣ε-eval Γ (⊢ε-refl Γ) (Uniε-purge (same Γ) Runi) Runi (≡-to-≣ε Γ (⊩ε-purge-refl Γ R)) ⟩
       Δ ⊩ε Γ ∋ εeval Γ (⊢ε-refl Γ) R
       ≣⟨ εeval-⊢ε-refl Γ Runi ⟩
       Δ ⊩ε Γ ∋ R
     Qed) ,
    ≣-refl σ r
