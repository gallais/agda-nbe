module stlcl.whnf.sound where

open import Data.Unit
open import Data.Sum
open import Data.Product

open import tools.contexts
open import tools.closures
open import stlcl.definition
open import stlcl.normalforms
open import stlcl.reductions
open import stlcl.whnf.model

open import Relation.Binary.PropositionalEquality renaming (subst to coerce ; subst₂ to coerce₂)

infix 2 [_⊩_]_↯ [_⊩'_]_↯_ [_⊩list_]_↯by_ [_⊩list'_]_↯_by_ [_⊩ε_]_↯


mutual

  [_⊩list'_]_↯_by_ : ∀ {n} Γ (σ : ty n) (t : Γ ⊢whnf `list σ) (XS : Γ ⊩' `list σ)
    (↯Σ : ∀ Γ (T : Γ ⊩ σ) → Set) → Set
  [ Γ ⊩list' σ ] xs ↯ `[] by ↯Σ = Γ ⊢ `list σ ∋ back-whnf xs ↝⋆ `[]
  [ Γ ⊩list' σ ] xs ↯ HD `∷ TL by ↯Σ =
     Γ ⊢ `list σ ∋ back-whnf xs ↝⋆ proj₁ HD `∷ proj₁ TL ×
     ↯Σ Γ HD × [ Γ ⊩list σ ] TL ↯by ↯Σ

  [_⊩list_]_↯by_ : ∀ {n} Γ (σ : ty n) (XS : Γ ⊩ `list σ) (↯Σ : ∀ Γ (T : Γ ⊩ σ) → Set) → Set
  [ Γ ⊩list σ ] t , inj₁ T ↯by ↯Σ = Γ ⊢ `list σ ∋ t ↝⋆ back-whne T
  [ Γ ⊩list σ ] t , inj₂ (t' , T) ↯by ↯Σ =
    Γ ⊢ `list σ ∋ t ↝⋆ back-whnf t' × [ Γ ⊩list' σ ] t' ↯ T by ↯Σ

mutual

  [_⊩'_]_↯_ : ∀ {n} Γ (σ : ty n) (t : Γ ⊢whnf σ) (T : Γ ⊩' σ) → Set
  [ Γ ⊩' `1 ] t ↯ T = ⊤
  [ Γ ⊩' `b k ] t ↯ T = Γ ⊢ `b k ∋ back-whnf t ↝⋆ back-whne T
  [ Γ ⊩' σ `→ τ ] f ↯ F =
    ∀ {Δ} (inc : Γ ⊆ Δ) {X} {fx} →
    Δ ⊢ τ ∋ fx ↝⋆ ⊢-weaken inc (back-whnf f) `$ proj₁ X →
    [ Δ ⊩ σ ] X ↯ → [ Δ ⊩ τ ] fx , proj₂ (F inc X) ↯
  [ Γ ⊩' σ `× τ ] t ↯ A , B =
    Γ ⊢ σ `× τ ∋ back-whnf t ↝⋆ proj₁ A `, proj₁ B ×
    [ Γ ⊩ σ ] A ↯ × [ Γ ⊩ τ ] B ↯
  [ Γ ⊩' `list σ ] t ↯ T = [ Γ ⊩list' σ ] t ↯ T by λ Γ X → [ Γ ⊩ σ ] X ↯

  [_⊩_]_↯ : ∀ {n} Γ (σ : ty n) (T : Γ ⊩ σ) → Set
  [ Γ ⊩ σ ] t , inj₁ T ↯ = Γ ⊢ σ ∋ t ↝⋆ back-whne T
  [ Γ ⊩ σ ] t , inj₂ (t' , T) ↯ = Γ ⊢ σ ∋ t ↝⋆ back-whnf t' × [ Γ ⊩' σ ] t' ↯ T

⊩↯list-fold : ∀ {n Γ} {σ : ty n} XS (cXS : [ Γ ⊩list σ ] XS ↯by λ Γ X → [ Γ ⊩ σ ] X ↯) →
  [ Γ ⊩ `list σ ] XS ↯
⊩↯list-fold (xs , inj₁ XS) cXS = cXS
⊩↯list-fold (xs , inj₂ XS) cXS = cXS

upward-⊩↯ : ∀ {n Γ} {σ : ty n} T {t u} → Γ ⊢ σ ∋ t ↝⋆ u → [ Γ ⊩ σ ] u , T ↯ → [ Γ ⊩ σ ] t , T ↯
upward-⊩↯ (inj₁ T) r cuT = ▹⋆-trans r cuT
upward-⊩↯ (inj₂ (t' , T)) r (rut' , ct'T) = ▹⋆-trans r rut' , ct'T

upward-⊩'↯ : ∀ {n} {Γ} (σ : ty n) T {t u} → Γ ⊢ σ ∋ back-whnf t ↝⋆ back-whnf u →
  [ Γ ⊩' σ ] u ↯ T → [ Γ ⊩' σ ] t ↯ T
upward-⊩'↯ `1 T rtu cuT = cuT
upward-⊩'↯ (`b k) T rtu ruT = ▹⋆-trans rtu ruT
upward-⊩'↯ (σ `× τ) T rtu (ruT , cuT) = ▹⋆-trans rtu ruT , cuT
upward-⊩'↯ (σ `→ τ) T {t} {u} rtu cuT =
  λ {Δ} inc {X} {fx} rfx cX →
  let r =
        Proof[ Δ ⊢ τ ]
          Δ ⊢ τ ∋ fx
          ↝⋆⟨ rfx ⟩
          Δ ⊢ τ ∋ ⊢-weaken inc (back-whnf t) `$ proj₁ X
          ↝⋆⟨ ▹⋆-cong `$₁ (↝⋆-weaken inc rtu) ⟩
          Δ ⊢ τ ∋ ⊢-weaken inc (back-whnf u) `$ proj₁ X
        Qed
  in cuT inc r cX
upward-⊩'↯ (`list σ) `[] rtu cuT = ▹⋆-trans rtu cuT
upward-⊩'↯ (`list σ) (HD `∷ (tl , inj₁ TL)) rtu (ru∷ , cHD , rtlTL) =
  ▹⋆-trans rtu ru∷ , cHD , rtlTL
upward-⊩'↯ (`list σ) (HD `∷ (tl , inj₂ TL)) rtu (ru∷ , cHD , cTL) =
  ▹⋆-trans rtu ru∷ , cHD , cTL

[_⊩ε_]_↯ : ∀ {n} (Δ Γ : Con (ty n)) (R : Δ ⊩ε Γ) → Set
[ Δ ⊩ε ε ] R ↯ = ⊤
[ Δ ⊩ε Γ ∙ σ ] R , r ↯ = [ Δ ⊩ε Γ ] R ↯ × [ Δ ⊩ σ ] r ↯

weaken-pull : ∀ {n} Γ {Δ Ε : Con (ty n)} (inc : Δ ⊆ Ε) R →
  ⊢ε-weaken Γ inc (pull Γ R) ≡ pull Γ (weaken-⊩ε Γ inc R)
weaken-pull ε inc R = refl
weaken-pull (Γ ∙ σ) inc (R , (r , inj₁ _)) rewrite weaken-pull Γ inc R = refl
weaken-pull (Γ ∙ σ) inc (R , (r , inj₂ _)) rewrite weaken-pull Γ inc R = refl

pull-Γ⊩ε : ∀ {n} (Γ : Con (ty n)) → pull Γ (Γ⊩ε Γ) ≡ ⊢ε-refl Γ
pull-Γ⊩ε ε = refl
pull-Γ⊩ε (Γ ∙ σ) =
  cong (λ ρ → ρ , `v here!) (trans (sym (weaken-pull Γ (step (same Γ)) (Γ⊩ε Γ)))
  (cong (⊢ε-weaken Γ (step (same Γ))) (pull-Γ⊩ε Γ)))

weaken-⊩-fst : ∀ {n Γ Δ} {σ : ty n} (inc : Γ ⊆ Δ) (T : Γ ⊩ σ) →
   proj₁ (weaken-⊩ inc T) ≡ ⊢-weaken inc (proj₁ T)
weaken-⊩-fst inc (t , inj₁ T) = refl
weaken-⊩-fst inc (t₁ , inj₂ (t₂ , T)) = refl

mutual

  weaken-⊩'↯list : ∀ {n Γ Δ} {σ : ty n} (inc : Γ ⊆ Δ) {↯Σ}
     (weaken-↯Σ : ∀ V → ↯Σ Γ V → ↯Σ Δ (weaken-⊩ inc V)) {xs} XS
     (cXS : [ Γ ⊩list' σ ] xs ↯ XS by ↯Σ) →
     [ Δ ⊩list' σ ] weaken-whnf inc xs ↯ weaken-⊩' (`list σ) inc XS by ↯Σ
  weaken-⊩'↯list {_} {Γ} {Δ} {σ} inc weaken-↯Σ {xs} `[] cXS =
    Proof[ Δ ⊢ `list σ ]
      Δ ⊢ `list σ ∋ back-whnf (weaken-whnf inc xs)
       ≡⟨ back-weaken-whnf inc xs ⟩
      Δ ⊢ `list σ ∋ ⊢-weaken inc (back-whnf xs)
       ↝⋆⟨ ↝⋆-weaken inc cXS ⟩
       Δ ⊢ `list σ ∋ `[]
    Qed
  weaken-⊩'↯list {_} {Γ} {Δ} {σ} inc weaken-↯Σ {xs} (HD `∷ (tl , inj₁ TL)) (rxs∷ , cHD , cTL) =
    let r =
          Proof[ Δ ⊢ `list σ ]
            Δ ⊢ `list σ ∋ back-whnf (weaken-whnf inc xs)
            ≡⟨ back-weaken-whnf inc xs ⟩
            Δ ⊢ `list σ ∋ ⊢-weaken inc (back-whnf xs)
            ↝⋆⟨ ↝⋆-weaken inc rxs∷ ⟩
            Δ ⊢ `list σ ∋ ⊢-weaken inc (proj₁ HD `∷ tl)
            ≡⟨ cong (λ hd → hd `∷ ⊢-weaken inc tl) (sym (weaken-⊩-fst inc HD)) ⟩
            Δ ⊢ `list σ ∋ proj₁ (weaken-⊩ inc HD) `∷ ⊢-weaken inc tl
          Qed
    in r ,
    weaken-↯Σ HD cHD ,
    ▹⋆-trans (↝⋆-weaken inc cTL) (≡-step (sym (back-weaken-whne inc TL)) refl)
  weaken-⊩'↯list {_} {Γ} {Δ} {σ} inc {↯Σ} weaken-↯Σ {xs} (HD `∷ (tl , inj₂ TL))
    (rxs∷ , cHD , rtlTL , cTL) =
    let r =
          Proof[ Δ ⊢ `list σ ]
          Δ ⊢ `list σ ∋ back-whnf (weaken-whnf inc xs)
            ≡⟨ back-weaken-whnf inc xs ⟩
            Δ ⊢ `list σ ∋ ⊢-weaken inc (back-whnf xs)
            ↝⋆⟨ ↝⋆-weaken inc rxs∷ ⟩
            Δ ⊢ `list σ ∋ ⊢-weaken inc (proj₁ HD `∷ tl)
            ≡⟨ cong (λ hd → hd `∷ ⊢-weaken inc tl) (sym (weaken-⊩-fst inc HD)) ⟩
            Δ ⊢ `list σ ∋ proj₁ (weaken-⊩ inc HD) `∷ ⊢-weaken inc tl
          Qed
    in
    r , weaken-↯Σ HD cHD ,
    ▹⋆-trans (↝⋆-weaken inc rtlTL) (≡-step (sym (back-weaken-whnf inc (proj₁ TL))) refl) ,
    (weaken-⊩'↯list inc weaken-↯Σ (proj₂ TL) cTL)

  weaken-⊩↯list : ∀ {n Γ Δ} {σ : ty n} (inc : Γ ⊆ Δ) {↯Σ}
     (weaken-↯Σ : ∀ V → ↯Σ Γ V → ↯Σ Δ (weaken-⊩ inc V)) XS (cXS : [ Γ ⊩list σ ] XS ↯by ↯Σ) →
     [ Δ ⊩list σ ] weaken-⊩ inc XS ↯by ↯Σ
  weaken-⊩↯list inc weaken-↯Σ (xs , inj₁ XS) rxsXS =
    ▹⋆-trans (↝⋆-weaken inc rxsXS) (≡-step (sym (back-weaken-whne inc XS)) refl)
  weaken-⊩↯list inc weaken-↯Σ (xs , inj₂ XS) (rxsXS , cXS) =
    ▹⋆-trans (↝⋆-weaken inc rxsXS) (≡-step (sym (back-weaken-whnf inc (proj₁ XS))) refl) ,
    weaken-⊩'↯list inc weaken-↯Σ (proj₂ XS) cXS

mutual

  weaken-⊩'↯ : ∀ {n Γ Δ} (σ : ty n) (inc : Γ ⊆ Δ) {x X} (cX : [ Γ ⊩' σ ] x ↯ X) →
     [ Δ ⊩' σ ] weaken-whnf inc x ↯ weaken-⊩' σ inc X
  weaken-⊩'↯ `1 inc cX = cX
  weaken-⊩'↯ {Δ = Δ} (`b k) inc {x} {X} cX =
    Proof[ Δ ⊢ `b k ]
     Δ ⊢ `b k ∋ back-whnf (weaken-whnf inc x)
     ≡⟨ back-weaken-whnf inc x ⟩
     Δ ⊢ `b k ∋ ⊢-weaken inc (back-whnf x)
     ↝⋆⟨ ↝⋆-weaken inc cX ⟩
     Δ ⊢ `b k ∋ ⊢-weaken inc (back-whne X)
     ≡⟨ sym (back-weaken-whne inc X) ⟩
     Δ ⊢ `b k ∋ back-whne (weaken-whne inc X)
   Qed
  weaken-⊩'↯ (σ `→ τ) inc {f} {F} cF =
    λ {Ε} inc' {X} {fx} red →
    let r : Ε ⊢ τ ∋ fx ↝⋆ ⊢-weaken (⊆-trans inc inc') (back-whnf f) `$ proj₁ X
        r =
          Proof[ Ε ⊢ τ ]
            Ε ⊢ τ ∋ fx
            ↝⋆⟨ red ⟩
            Ε ⊢ τ ∋ ⊢-weaken inc' (back-whnf (weaken-whnf inc f)) `$ proj₁ X
            ≡⟨ cong (λ f → ⊢-weaken inc' f `$ proj₁ X) (back-weaken-whnf inc f) ⟩
            Ε ⊢ τ ∋ ⊢-weaken inc' (⊢-weaken inc (back-whnf f)) `$ proj₁ X
            ≡⟨ cong (λ f → f `$ proj₁ X) (⊢-weaken² inc inc' (back-whnf f)) ⟩
            Ε ⊢ τ ∋ ⊢-weaken (⊆-trans inc inc') (back-whnf f) `$ proj₁ X
          Qed
    in cF (⊆-trans inc inc') r
  weaken-⊩'↯ {_} {Γ} {Δ} (σ `× τ) inc {p} {(a , A) , (b , B)} (rAB , cA , cB) =
    let r =
          Proof[ Δ ⊢ σ `× τ ]
          Δ ⊢ σ `× τ ∋ back-whnf (weaken-whnf inc p)
          ≡⟨ back-weaken-whnf inc p ⟩
          Δ ⊢ σ `× τ ∋ ⊢-weaken inc (back-whnf p)
          ↝⋆⟨ ↝⋆-weaken inc rAB ⟩
          Δ ⊢ σ `× τ ∋ ⊢-weaken inc a `, ⊢-weaken inc b
          ≡⟨ cong₂ _`,_ (sym (weaken-⊩-fst inc (a , A))) (sym (weaken-⊩-fst inc (b , B))) ⟩
          Δ ⊢ σ `× τ ∋ proj₁ (weaken-⊩ inc (a , A)) `, proj₁ (weaken-⊩ inc (b , B))
          Qed
    in r , weaken-⊩↯ inc (a , A) cA , weaken-⊩↯ inc (b , B) cB
  weaken-⊩'↯ (`list σ) inc {xs} {XS} cXS = weaken-⊩'↯list inc (weaken-⊩↯ inc) XS cXS

  weaken-⊩↯ : ∀ {n Γ Δ} {σ : ty n} (inc : Γ ⊆ Δ) X (cX : [ Γ ⊩ σ ] X ↯) → [ Δ ⊩ σ ] weaken-⊩ inc X ↯
  weaken-⊩↯ inc (x , inj₁ X) rxX =
    ▹⋆-trans (↝⋆-weaken inc rxX) (≡-step (sym (back-weaken-whne inc X)) refl)
  weaken-⊩↯ {σ = σ} inc (x , inj₂ X) (rxX , cX) =
    ▹⋆-trans (↝⋆-weaken inc rxX) (≡-step (sym (back-weaken-whnf inc (proj₁ X))) refl) ,
    weaken-⊩'↯ σ inc cX

weaken-⊩ε↯ : ∀ {n} {Δ Ε : Con (ty n)} Γ (inc : Δ ⊆ Ε) R (cR : [ Δ ⊩ε Γ ] R ↯) →
  [ Ε ⊩ε Γ ] weaken-⊩ε Γ inc R ↯
weaken-⊩ε↯ ε inc R cR = cR
weaken-⊩ε↯ (Γ ∙ σ) inc (R , r) (cR , cr) = weaken-⊩ε↯ Γ inc R cR , weaken-⊩↯ inc  r cr

infix 2 [_]↝⋆↑_when_ 

[_]_↯↓whne : ∀ {n Γ} (σ : ty n) (t : Γ ⊢whne σ) → [ Γ ⊩ σ ] ↓[ σ ] t ↯
[ σ ] t ↯↓whne = refl

[_]↝⋆↑_when_ : ∀ {n Γ} (σ : ty n) T (r : [ Γ ⊩ σ ] T ↯) → Γ ⊢ σ ∋ proj₁ T ↝⋆ back-whnf (↑[ σ ] T)
[ σ ]↝⋆↑ u , inj₁ T when r = r
[ σ ]↝⋆↑ u , inj₂ T when (r , _) = r


Γ⊩ε↯ : ∀ {n} (Γ : Con (ty n)) → [ Γ ⊩ε Γ ] Γ⊩ε Γ ↯
Γ⊩ε↯ ε = tt
Γ⊩ε↯ (Γ ∙ σ) = weaken-⊩ε↯ Γ (step (same Γ)) _ (Γ⊩ε↯ Γ) , [ σ ] `v here! ↯↓whne

lookup-fst : ∀ {n Γ Δ} {σ : ty n} (pr : σ ∈ Γ) (R : Δ ⊩ε Γ) → proj₁ (lookup pr R) ≡ get pr (pull Γ R)
lookup-fst here! (_  , r) = refl
lookup-fst (there pr) (R , _) = lookup-fst pr R

`$'-fst : ∀ {n Γ} {σ τ : ty n} (F : Γ ⊩ σ `→ τ) X → proj₁ (F `$' X) ≡ proj₁ F `$ proj₁ X
`$'-fst (f , inj₁ F) (x , X) = refl
`$'-fst (f₁ , inj₂ (f₂ , F)) (x , X) = refl

`π₁'-fst : ∀ {n Γ} {σ τ : ty n} (P : Γ ⊩ σ `× τ) → proj₁ (`π₁' P) ≡ `π₁ (proj₁ P)
`π₁'-fst (p , inj₁ P) = refl
`π₁'-fst (p₁ , inj₂ (p₂ , P)) = refl

`π₂'-fst : ∀ {n Γ} {σ τ : ty n} (P : Γ ⊩ σ `× τ) → proj₁ (`π₂' P) ≡ `π₂ (proj₁ P)
`π₂'-fst (p , inj₁ P) = refl
`π₂'-fst (p₁ , inj₂ (p₂ , P)) = refl

`++'-fst : ∀ {n Γ} {σ : ty n} (XS YS : Γ ⊩ `list σ) → proj₁ (XS `++' YS) ≡ proj₁ XS `++ proj₁ YS
`++'-fst (xs , inj₁ XS) (ys , YS) = refl
`++'-fst (xs₁ , inj₂ (xs₂ , `[])) (ys , YS) = refl
`++'-fst (xs₁ , inj₂ (xs₂ , (hd , HD) `∷ TL')) (ys , YS) = refl

`map'-fst : ∀ {n Γ} {σ τ : ty n} (F : Γ ⊩ σ `→ τ) XS → proj₁ (`map' F XS) ≡ `map (proj₁ F) (proj₁ XS)
`map'-fst (f , F) (xs , inj₁ XS) = refl
`map'-fst (f , F) (xs , inj₂ (xs₂ , `[])) = refl
`map'-fst (f , F) (xs , inj₂ (xs₂ , (hd , HD) `∷ TL')) = refl

`fold'-fst : ∀ {n Γ} {σ τ : ty n} (C : Γ ⊩ σ `→ τ `→ τ) N XS →
  proj₁ (`fold' C N XS) ≡ `fold (proj₁ C) (proj₁ N) (proj₁ XS)
`fold'-fst (c , C) (n , N) (xs , inj₁ XS) = refl
`fold'-fst (c , C) (n , N) (xs , inj₂ (xs₂ , `[])) = refl
`fold'-fst (c , C) (n , N) (xs , inj₂ (xs₂ , (hd , HD) `∷ TL')) = refl

eval-fst : ∀ {n Γ Δ} {σ : ty n} (t : Γ ⊢ σ) (R : Δ ⊩ε Γ) → proj₁ (eval t R) ≡ subst t (pull Γ R)
eval-fst (`v pr) R = lookup-fst pr R
eval-fst (`λ t) R = refl
eval-fst (f `$ x) R rewrite `$'-fst (eval f R) (eval x R)
                            | eval-fst f R | eval-fst x R = refl
eval-fst `⟨⟩ R = refl
eval-fst (a `, b) R rewrite eval-fst a R | eval-fst b R = refl
eval-fst (`π₁ t) R rewrite `π₁'-fst (eval t R) | eval-fst t R = refl
eval-fst (`π₂ t) R rewrite `π₂'-fst (eval t R) | eval-fst t R = refl
eval-fst `[] R = refl
eval-fst (hd `∷ tl) R rewrite eval-fst hd R | eval-fst tl R = refl
eval-fst (xs `++ ys) R rewrite `++'-fst (eval xs R) (eval ys R)
                               | eval-fst xs R | eval-fst ys R = refl
eval-fst (`map f xs) R rewrite `map'-fst (eval f R) (eval xs R)
                               | eval-fst f R | eval-fst xs R = refl
eval-fst (`fold c n xs) R rewrite `fold'-fst (eval c R) (eval n R) (eval xs R)
                                  | eval-fst c R | eval-fst n R | eval-fst xs R = refl

infix 2 _`$'_↯by_and_ `π₁'_↯by_ `π₂'_↯by_ _`∷'_↯by_and_ _`,'_↯by_and_ _`++'_↯by_and_

_`$'_↯by_and_ : ∀ {n Γ} {σ τ : ty n} F X (cF : [ Γ ⊩ σ `→ τ ] F ↯)
  (cX : [ Γ ⊩ σ ] X ↯) → [ Γ ⊩ τ ] F `$' X ↯
f , inj₁ F `$' x , X ↯by cF and cX = ▹⋆-cong `$₁ cF
f , inj₂ (g , F) `$' x , X ↯by cfg , cF and cX =
  let red : _ ⊢ _ ∋ f `$ x ↝⋆ ⊢-weaken (same _) (back-whnf g) `$ x
      red =
        Proof[ _ ⊢ _ ]
          _ ⊢ _ ∋ f `$ x
          ↝⋆⟨ ▹⋆-cong `$₁ cfg ⟩
          _ ⊢ _ ∋ back-whnf g `$ x
          ≡⟨ cong (λ f → f `$ x) (sym (⊢-weaken-refl (back-whnf g))) ⟩
          _ ⊢ _ ∋ ⊢-weaken (same _) (back-whnf g) `$ x
        Qed in
  cF (same _) red cX

_`,'_↯by_and_ : ∀ {n Γ} {σ τ : ty n} A B (cA : [ Γ ⊩ σ ] A ↯) (cB : [ Γ ⊩ τ ] B ↯) →
  [ Γ ⊩ σ `× τ ] A `,' B ↯
a , A `,' b , B ↯by cA and cB = refl , refl , cA , cB

`π₁'_↯by_ : ∀ {n Γ} {σ τ : ty n} P (cP : [ Γ ⊩ σ `× τ ] P ↯) → [ Γ ⊩ σ ] `π₁' P ↯
`π₁' p , inj₁ P ↯by cP = ▹⋆-cong `π₁ cP
`π₁' p₁ , inj₂ (p₂ , A , B) ↯by (rp₁₂ , rp₂P , cA , cB) =
  let r =
        Proof[ _ ⊢ _ ]
          _ ⊢ _ ∋ `π₁ p₁
          ↝⋆⟨ ▹⋆-cong `π₁ (▹⋆-trans rp₁₂ rp₂P) ⟩
          _ ⊢ _ ∋ `π₁ (proj₁ A `, proj₁ B)
          ↝⟨ `βπ₁ ⟩
          _ ⊢ _ ∋ proj₁ A
        Qed
  in upward-⊩↯ (proj₂ A) r cA

`π₂'_↯by_ : ∀ {n Γ} {σ τ : ty n} P (cP : [ Γ ⊩ σ `× τ ] P ↯) → [ Γ ⊩ τ ] `π₂' P ↯
`π₂' p , inj₁ P ↯by cP = ▹⋆-cong `π₂ cP
`π₂' p₁ , inj₂ (p₂ , A , B) ↯by (rp₁₂ , rp₂P , cA , cB) =
  let r =
        Proof[ _ ⊢ _ ]
          _ ⊢ _ ∋ `π₂ p₁
          ↝⋆⟨ ▹⋆-cong `π₂ (▹⋆-trans rp₁₂ rp₂P) ⟩
          _ ⊢ _ ∋ `π₂ (proj₁ A `, proj₁ B)
          ↝⟨ `βπ₂ ⟩
          _ ⊢ _ ∋ proj₁ B
        Qed
  in upward-⊩↯ (proj₂ B) r cB

_`∷'_↯by_and_ : ∀ {n Γ} {σ : ty n} HD TL (cHD : [ Γ ⊩ σ ] HD ↯) (cTL : [ Γ ⊩ `list σ ] TL ↯) →
  [ Γ ⊩ `list σ ] HD `∷' TL ↯
hd , HD `∷' tl , inj₁ TL ↯by cHD and cTL = refl , refl , cHD , cTL
hd , HD `∷' tl , inj₂ TL ↯by cHD and cTL = refl , refl , cHD , cTL

_`++'_↯by_and_ : ∀ {n Γ} {σ : ty n} (XS : Γ ⊩ `list σ) (YS : Γ ⊩ `list σ)
  (cXS : [ Γ ⊩ `list σ ] XS ↯) (cYS : [ Γ ⊩ `list σ ] YS ↯) → [ Γ ⊩ `list σ ] XS `++' YS ↯
xs , inj₁ XS `++' YS ↯by cXS and cYS = ▹⋆-cong `++₁ cXS
xs₁ , inj₂ (xs₂ , `[]) `++' ys , YS ↯by rxs₁₂ , rxs[] and cYS =
  let r =
        Proof[ _ ⊢ `list _ ]
          _ ⊢ _ ∋ xs₁ `++ ys
          ↝⋆⟨ ▹⋆-cong `++₁ (▹⋆-trans rxs₁₂ rxs[]) ⟩
          _ ⊢ _ ∋ `[] `++ ys
          ↝⟨ `β++₁ ⟩
          _ ⊢ _ ∋ ys
        Qed
  in upward-⊩↯ YS r cYS
xs₁ , inj₂ (xs₂ , HD `∷ TL) `++' YS ↯by (rxs₁₂ , rxs₂∷ , cHD , cTL) and cYS =
  let cTL++YS    = TL `++' YS ↯by ⊩↯list-fold TL cTL and cYS
      cHD∷TL++YS = HD `∷' (TL `++' YS) ↯by cHD and cTL++YS
      r =
        Proof[ _ ⊢ `list _ ]
          _ ⊢ _ ∋ xs₁ `++ proj₁ YS
          ↝⋆⟨ ▹⋆-cong `++₁ (▹⋆-trans rxs₁₂ rxs₂∷) ⟩
          _ ⊢ _ ∋ (proj₁ HD `∷ proj₁ TL) `++ proj₁ YS
          ↝⟨ `β++₂ ⟩
          _ ⊢ _ ∋ proj₁ HD `∷ (proj₁ TL `++ proj₁ YS)
          ≡⟨ cong (_`∷_ (proj₁ HD)) (sym (`++'-fst TL YS)) ⟩
          _ ⊢ _ ∋ proj₁ HD `∷ proj₁ (TL `++' YS)
        Qed
  in upward-⊩↯ (proj₂ (HD `∷' (TL `++' YS))) r cHD∷TL++YS

`map'-↯ : ∀ {n Γ} {σ τ : ty n} F XS (cF : [ Γ ⊩ σ `→ τ ] F ↯) (cXS : [ Γ ⊩ `list σ ] XS ↯) →
  [ Γ ⊩ `list τ ] `map' F XS ↯
`map'-↯ (f , F) (xs , inj₁ XS) cF cXS = ▹⋆-cong `map₂ cXS
`map'-↯ {_} {Γ} {σ} {τ} (f , F) (xs₁ , inj₂ (xs₂ , `[])) cF (rxs₁₂ , rxs₂[]) =
  let r =
        Proof[ Γ ⊢ `list τ ]
          Γ ⊢ `list τ ∋ `map f xs₁
          ↝⋆⟨ ▹⋆-cong `map₂ (▹⋆-trans rxs₁₂ rxs₂[]) ⟩
          Γ ⊢ `list τ ∋ `map f `[]
          ↝⟨ `βmap₁ ⟩
          Γ ⊢ `list τ ∋ `[]
        Qed
  in r , refl
`map'-↯ {_} {Γ} {σ} {τ} F (xs₁ , inj₂ (xs₂ , HD `∷ TL)) cF (rxs₁₂ , rxs₂∷ , cHD , cTL) =
  let cF$HD        = F `$' HD ↯by cF and cHD
      cmapFTL      = `map'-↯ F TL cF (⊩↯list-fold TL cTL)
      cF$HD∷mapFTL = (F `$' HD) `∷' (`map' F TL) ↯by cF$HD and cmapFTL
      r =
        Proof[ Γ ⊢ `list τ ]
          Γ ⊢ `list τ ∋ `map (proj₁ F) xs₁
          ↝⋆⟨ ▹⋆-cong `map₂ (▹⋆-trans rxs₁₂ rxs₂∷) ⟩
          Γ ⊢ `list τ ∋ `map (proj₁ F) (proj₁ HD `∷ proj₁ TL)
          ↝⟨ `βmap₂ ⟩
          Γ ⊢ `list τ ∋ (proj₁ F `$ proj₁ HD) `∷ `map (proj₁ F) (proj₁ TL)
          ≡⟨ cong₂ _`∷_ (sym (`$'-fst F HD)) (sym (`map'-fst F TL)) ⟩
          Γ ⊢ `list τ ∋ proj₁ (F `$' HD) `∷ proj₁ (`map' F TL)
        Qed
  in upward-⊩↯ (proj₂ ((F `$' HD) `∷' (`map' F TL))) r cF$HD∷mapFTL

`fold'-↯ : ∀ {n Γ} {σ τ : ty n} C N XS (cC : [ Γ ⊩ σ `→ τ `→ τ ] C ↯) (cN : [ Γ ⊩ τ ] N ↯)
  (cXS : [ Γ ⊩ `list σ ] XS ↯) → [ Γ ⊩ τ ] `fold' C N XS ↯
`fold'-↯ C N (xs , inj₁ XS) cC cN cXS = ▹⋆-cong `fold₃ cXS
`fold'-↯ {_} {Γ} {σ} {τ} (c , C) (n , N) (xs₁ , inj₂ (xs₂ , `[])) cC cN (rxs₁₂ , rxs₂[]) =
  let r =
        Proof[ Γ ⊢ τ ]
          Γ ⊢ τ ∋ `fold c n xs₁
          ↝⋆⟨ ▹⋆-cong `fold₃ (▹⋆-trans rxs₁₂  rxs₂[]) ⟩
          Γ ⊢ τ ∋ `fold c n `[]
          ↝⟨ `βfold₁ ⟩
          Γ ⊢ τ ∋ n
        Qed
  in upward-⊩↯ N r cN
`fold'-↯ {_} {Γ} {σ} {τ} C N (xs₁ , inj₂ (xs₂ , HD `∷ TL)) cC cN (rxs₁₂ , rxs₂∷ , cHD , cTL) =
   let cC$HD      = C `$' HD ↯by cC and cHD
       cfoldCNTL  = `fold'-↯ C N TL cC cN (⊩↯list-fold TL cTL)
       cC$HD$fold = (C `$' HD) `$' (`fold' C N TL) ↯by cC$HD and cfoldCNTL
       r =
         Proof[ Γ ⊢ τ ]
           Γ ⊢ τ ∋ `fold (proj₁ C) (proj₁ N) xs₁
           ↝⋆⟨ ▹⋆-cong `fold₃ (▹⋆-trans rxs₁₂ rxs₂∷) ⟩
           Γ ⊢ τ ∋ `fold (proj₁ C) (proj₁ N) (proj₁ HD `∷ proj₁ TL)
           ↝⟨ `βfold₂ ⟩
           Γ ⊢ τ ∋ proj₁ C `$ proj₁ HD `$ `fold (proj₁ C) (proj₁ N) (proj₁ TL)
           ≡⟨ cong (λ t → proj₁ C `$ proj₁ HD `$ t) (sym (`fold'-fst C N TL)) ⟩
           Γ ⊢ τ ∋ proj₁ C `$ proj₁ HD `$ proj₁ (`fold' C N TL)
           ≡⟨ cong (λ cn → cn `$ proj₁ (`fold' C N TL)) (sym (`$'-fst C HD)) ⟩
           Γ ⊢ τ ∋ proj₁ (C `$' HD) `$ proj₁ (`fold' C N TL)
           ≡⟨ sym (`$'-fst (C `$' HD) (`fold' C N TL)) ⟩
           Γ ⊢ τ ∋ proj₁ (C `$' HD `$' `fold' C N TL)
         Qed
   in upward-⊩↯ (proj₂ (C `$' HD `$' `fold' C N TL)) r cC$HD$fold

lookup-↯ : ∀ {n Γ} {σ : ty n} (pr : σ ∈ Γ) {Δ} R (cR : [ Δ ⊩ε Γ ] R ↯) → [ Δ ⊩ σ ] lookup pr R ↯
lookup-↯ here! (_ , r) (_ , cr) = cr
lookup-↯ (there pr) (R , _) (cR , _) = lookup-↯ pr R cR

eval-↯ : ∀ {n Γ} {σ : ty n} (t : Γ ⊢ σ) {Δ} R (cR : [ Δ ⊩ε Γ ] R ↯) → [ Δ ⊩ σ ] eval t R ↯
eval-↯ (`v pr) R cR = lookup-↯ pr R cR
eval-↯ {_} {Γ} {σ `→ τ} (`λ t) {Δ} R cR =
  refl , (λ {Ε} inc {X} {fx} rfx cX →
  let IH = eval-↯ t (weaken-⊩ε Γ inc R , X) (weaken-⊩ε↯ Γ inc R cR , cX)
      r : Ε ⊢ τ ∋ fx ↝⋆ proj₁ (eval t (weaken-⊩ε Γ inc R , X))
      r = 
        Proof[ Ε ⊢ τ ]
          Ε ⊢ τ ∋ fx
          ↝⋆⟨ rfx ⟩
          Ε ⊢ τ ∋ _
          ↝⟨ `βλ ⟩
          Ε ⊢ τ ∋ subst (⊢-weaken (pop! inc) (subst t _)) (⊢ε-refl Ε , proj₁ X)
          ≡⟨ subst-weaken (pop! inc) (subst t _) _ ⟩
          Ε ⊢ τ ∋ subst (subst t _) _
          ≡⟨ subst² t _ (purge inc (⊢ε-refl Ε) , proj₁ X) ⟩
          Ε ⊢ τ ∋ subst t _
          ≡⟨ cong (λ ρ → subst t (ρ , proj₁ X))
                  (⊢ε²-step Γ (same _) (pull Γ R) (purge inc (⊢ε-refl Ε)) (proj₁ X)) ⟩
          Ε ⊢ τ ∋ subst t _
          ≡⟨ cong₂ (λ ρ₁ ρ₂ → subst t (⊢ε² Γ ρ₁ ρ₂ , proj₁ X))
                  (⊢ε-weaken-refl Γ (pull Γ R)) (purge-⊢ε-refl inc) ⟩
          Ε ⊢ τ ∋ subst t _
          ≡⟨ cong (λ ρ → subst t (ρ , proj₁ X)) (sym (⊢ε²-weaken Γ inc (pull Γ R) (⊢ε-refl Δ))) ⟩
          Ε ⊢ τ ∋ subst t _
          ≡⟨ cong (λ ρ → subst t (⊢ε-weaken Γ inc ρ , proj₁ X)) (⊢ε²-refl Γ (pull Γ R)) ⟩
           Ε ⊢ τ ∋ subst t _
          ≡⟨ cong (λ ρ → subst t (ρ , proj₁ X)) (weaken-pull Γ inc R) ⟩
          Ε ⊢ τ ∋ subst t (pull (Γ ∙ σ) (weaken-⊩ε Γ inc R , X))
          ≡⟨ sym (eval-fst t (weaken-⊩ε Γ inc R , X)) ⟩
          Ε ⊢ τ ∋ proj₁ (eval t (weaken-⊩ε Γ inc R , X))
        Qed
  in upward-⊩↯ (proj₂ (eval t (weaken-⊩ε Γ inc R , X))) r IH)
eval-↯ (f `$ x) R cR = eval f R `$' eval x R ↯by eval-↯ f R cR and eval-↯ x R cR
eval-↯ `⟨⟩ R cR = refl , tt
eval-↯ {_} {Γ} {σ `× τ} (a `, b) {Δ} R cR = eval a R `,' eval b R ↯by eval-↯ a R cR and eval-↯ b R cR
eval-↯ (`π₁ t) R cR = `π₁' eval t R ↯by eval-↯ t R cR
eval-↯ (`π₂ t) R cR = `π₂' eval t R ↯by eval-↯ t R cR
eval-↯ `[] R cR = refl , refl
eval-↯ (hd `∷ tl) R cR = eval hd R `∷' eval tl R ↯by eval-↯ hd R cR and eval-↯ tl R cR
eval-↯ (xs `++ ys) R cR = eval xs R `++' eval ys R ↯by eval-↯ xs R cR and eval-↯ ys R cR
eval-↯ (`map f xs) R cR = `map'-↯ (eval f R) (eval xs R) (eval-↯ f R cR) (eval-↯ xs R cR)
eval-↯ (`fold c n xs) R cR =
  `fold'-↯ (eval c R) (eval n R) (eval xs R) (eval-↯ c R cR) (eval-↯ n R cR) (eval-↯ xs R cR)

soundness : ∀ {n Γ} {σ : ty n} t → Γ ⊢ σ ∋ t ↝⋆ back-whnf (wh-norm t)
soundness {_} {Γ} {σ} t =
  Proof[ Γ ⊢ σ ]
    Γ ⊢ σ ∋ t
    ≡⟨ sym (subst-refl t) ⟩
    Γ ⊢ σ ∋ subst t (⊢ε-refl Γ)
    ≡⟨ cong (subst t) (sym (pull-Γ⊩ε Γ)) ⟩
    Γ ⊢ σ ∋ subst t (pull Γ (Γ⊩ε Γ))
    ≡⟨ sym (eval-fst t (Γ⊩ε Γ)) ⟩
    Γ ⊢ σ ∋ proj₁ (eval t (Γ⊩ε Γ))
    ↝⋆⟨ [ σ ]↝⋆↑ eval t (Γ⊩ε Γ) when eval-↯ t (Γ⊩ε Γ) (Γ⊩ε↯ Γ) ⟩
    Γ ⊢ σ ∋ back-whnf (↑[ σ ] eval t (Γ⊩ε Γ))
  Qed