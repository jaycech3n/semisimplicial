{-# OPTIONS --without-K #-}

{- Working through the standard attempt to constructing semisimplicial types -}

module SST where

open import lib.Basics
open import lib.types.Unit
open import lib.types.Nat

record ⊤₁ : Type₁ where
  instance constructor tt₁

data Fin : ℕ → Set where
  fz : {n : ℕ} → Fin (S n)
  fs : {n : ℕ} → Fin n → Fin (S n)

_<Fin_ : {n : ℕ} → Fin n → Fin n → Set
i <Fin fz = ⊥
fz <Fin fs _ = ⊤
fs i <Fin fs j = i <Fin j

is-increasing : {m n : ℕ} → (Fin m → Fin n) → Set
is-increasing {m} f = {i j : Fin m} → i <Fin j → f i <Fin f j

_→+_ : ℕ → ℕ → Set
m →+ n = Σ (Fin m → Fin n) is-increasing

infixr 80 _∘+_
_∘+_ : {m n k : ℕ} → (n →+ k) → (m →+ n) → m →+ k
(g , inc-g) ∘+ (f , inc-f) = ((g ∘ f) , inc-g ∘ inc-f) -- strictly associative!


-- General lemmas

transp-λ : {A B : Set} {C : A → B → Set}
           {a₁ a₂ : A} (p : a₁ == a₂) (f : (b : B) → C a₁ b)
           → transport (λ a → (b : B) → C a b) p f
             == λ b → transport (λ a → C a b) p (f b)
transp-λ idp f = idp

transp-ap : {A B : Set} (P : B → Set) (f : A → B) {a₁ a₂ : A} (p : a₁ == a₂)
            → transport (P ∘ f) p == transport P (ap f p)
transp-ap P f idp = idp


-- Semisimplicial types

-- SST n is the type of (n-1)-truncated semisimplicial types, i.e. "Σ X₀ ... Xₙ₋₁"
SST  : (n : ℕ) → Set₁
-- Sk k X n is the (k-1)-skeleton of a (n-1)-simplex
Sk   : (k : ℕ) → SST k → ℕ → Set
Sk→  : (k : ℕ) (X : SST k) {m n : ℕ} → (m →+ n) → Sk k X n → Sk k X m
Sk→∘ : (k : ℕ) (X : SST k) {n₁ n₂ n₃ : ℕ} (f : n₁ →+ n₂) (g : n₂ →+ n₃) (x : Sk k X n₃)
       → Sk→ k X (g ∘+ f) x == Sk→ k X f (Sk→ k X g x)

Sk→∘-coh : (k : ℕ) (X : SST k)
           {n₁ n₂ n₃ n₄ : ℕ} (e : n₁ →+ n₂) (f : n₂ →+ n₃) (g : n₃ →+ n₄)
           (x : Sk k X n₄)
           → (Sk→∘ k X e (g ∘+ f) x ∙ ap (Sk→ k X e) (Sk→∘ k X f g x))
             ==
             (Sk→∘ k X (f ∘+ e) g x ∙ Sk→∘ k X e f (Sk→ k X g x))

-- pointless formulation
Sk→∘' : (k : ℕ) (X : SST k) {n₁ n₂ n₃ : ℕ} (f : n₁ →+ n₂) (g : n₂ →+ n₃)
       → Sk→ k X (g ∘+ f) == Sk→ k X f ∘ Sk→ k X g

Sk→∘-coh' : (k : ℕ) (X : SST k)
           {n₁ n₂ n₃ n₄ : ℕ} (e : n₁ →+ n₂) (f : n₂ →+ n₃) (g : n₃ →+ n₄)
           → Sk→∘' k X e (g ∘+ f) ∙ (Sk→∘' k X f g |in-ctx (Sk→ k X e ∘_))
             ==
             Sk→∘' k X (f ∘+ e) g ∙ (Sk→∘' k X e f |in-ctx (_∘ Sk→ k X g))

SST O = ⊤₁
SST (S k) = Σ (SST k) λ X →
              Sk k X (S k) → Set

Sk O _ n = ⊤
Sk (S k) (X , Y) n = Σ (Sk k X n) λ x →
                       (f : (S k) →+ n) → Y (Sk→ k X f x)

Sk→ O _ _  x = x
Sk→ (S k) (X , Y) g (x , F) =
  (Sk→ k X g x , λ f → transport Y (Sk→∘ k X f g x) (F (g ∘+ f)))

Sk→∘ O _ _ _ _ = idp
Sk→∘ (S k) (X , Y) {n₁} g f (x , F) = pair= (Sk→∘ k X g f x) (
  from-transp (λ x' → (f' : S k →+ n₁) → Y (Sk→ k X f' x')) (Sk→∘ k X g f x) (

    transport (λ x' → (f' : S k →+ n₁) → Y (Sk→ k X f' x')) (Sk→∘ k X g f x)
      (λ h → transport Y (Sk→∘ k X h (f ∘+ g) x) (F ((f ∘+ g) ∘+ h)))

    =⟨ transp-λ (Sk→∘ k X g f x)
         (λ h → transport Y (Sk→∘ k X h (f ∘+ g) x) (F ((f ∘+ g) ∘+ h))) ⟩

    (λ h →
         transport (λ x' → Y (Sk→ k X h x')) (Sk→∘ k X g f x)
           (transport Y (Sk→∘ k X h (f ∘+ g) x) (F ((f ∘+ g) ∘+ h))))

    =⟨ λ= ptwise= ⟩

    (λ h →
         transport Y (Sk→∘ k X h g (Sk→ k X f x))
           (transport Y (Sk→∘ k X (g ∘+ h) f x) (F (f ∘+ g ∘+ h))))

    =∎
    )
  )
  where
    ptwise= : (h : S k →+ n₁)
              → transport (λ x' → Y (Sk→ k X h x')) (Sk→∘ k X g f x)
                  (transport Y (Sk→∘ k X h (f ∘+ g) x) (F ((f ∘+ g) ∘+ h)))
                ==
                transport Y (Sk→∘ k X h g (Sk→ k X f x))
                  (transport Y (Sk→∘ k X (g ∘+ h) f x) (F (f ∘+ g ∘+ h)))
    ptwise= h =

      transport (λ x' → Y (Sk→ k X h x')) (Sk→∘ k X g f x)
        (transport Y (Sk→∘ k X h (f ∘+ g) x) (F ((f ∘+ g) ∘+ h)))

      =⟨ transp-ap Y (Sk→ k X h) (Sk→∘ k X g f x)
       |in-ctx (λ tr → tr (transport Y (Sk→∘ k X h (f ∘+ g) x) (F ((f ∘+ g) ∘+ h)))) ⟩

      transport Y (ap (Sk→ k X h) (Sk→∘ k X g f x))
        (transport Y (Sk→∘ k X h (f ∘+ g) x) (F ((f ∘+ g) ∘+ h)))

      =⟨ ! (transp-∙ (Sk→∘ k X h (f ∘+ g) x) (ap (Sk→ k X h) (Sk→∘ k X g f x))
                     (F ((f ∘+ g) ∘+ h))) ⟩

      transport Y ((Sk→∘ k X h (f ∘+ g) x) ∙ (ap (Sk→ k X h) (Sk→∘ k X g f x)))
        (F ((f ∘+ g) ∘+ h))

      =⟨ Sk→∘-coh k X h g f x |in-ctx (λ p → transport Y p _) ⟩

      transport Y ((Sk→∘ k X (g ∘+ h) f x) ∙ (Sk→∘ k X h g (Sk→ k X f x)))
        (F (f ∘+ g ∘+ h))

      =⟨ transp-∙ (Sk→∘ k X (g ∘+ h) f x) (Sk→∘ k X h g (Sk→ k X f x))
                  (F (f ∘+ g ∘+ h)) ⟩

      transport Y (Sk→∘ k X h g (Sk→ k X f x))
        (transport Y (Sk→∘ k X (g ∘+ h) f x) (F (f ∘+ g ∘+ h)))

      =∎

Sk→∘' k X f g = λ= (Sk→∘ k X f g)

Sk→∘-coh' O X e f g = idp
Sk→∘-coh' (S k) (X , Y) e f g = {!!}

-- Composition of equalities on functions
ap∙ap : {A B : Set} {e f g h : A → B}
        (p : e == f) (q : f == h)
        (r : e == g) (s : g == h)
        (x : A)
        → p ∙ q == r ∙ s
        → ap (λ ϕ → ϕ x) p ∙ ap (λ ϕ → ϕ x) q == ap (λ ϕ → ϕ x) r ∙ ap (λ ϕ → ϕ x) s
ap∙ap idp q idp s x α = ap (ap (λ ϕ → ϕ x)) α

Sk→∘-coh k X e f g x = {!ap∙ap (Sk→∘' k X e (g ∘+ f)) {!!} {!!} {!!} x (Sk→∘-coh' k X e f g)!}
