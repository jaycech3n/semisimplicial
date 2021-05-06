{-# OPTIONS --without-K --termination-depth=2 #-}

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

-- Composition of equalities on functions
ap∙ap : {A B : Set} {e f g h : A → B}
        (p : e == f) (q : f == h)
        (r : e == g) (s : g == h)
        (x : A)
        → p ∙ q == r ∙ s
        → ap (λ ϕ → ϕ x) p ∙ ap (λ ϕ → ϕ x) q == ap (λ ϕ → ϕ x) r ∙ ap (λ ϕ → ϕ x) s
ap∙ap idp q idp s x α = ap (ap (λ ϕ → ϕ x)) α

ap-app-l : {A B C : Set} {f g : A → B} (h : B → C) (p : f == g) (x : A)
           → ap (λ u → u x) (ap (h ∘_) p) == ap h (app= p x)
ap-app-l h idp x = idp

ap-app-r : {A B C : Set} {f g : B → C} (h : A → B) (p : f == g) (x : A)
           → ap (λ u → u x) (ap (_∘ h) p) == app= p (h x)
ap-app-r h idp x = idp


-- Semisimplicial types

-- SST n is the type of (n-1)-truncated semisimplicial types, i.e. "Σ X₀ ... Xₙ₋₁"
SST  : (n : ℕ) → Set₁
-- Sk k X n is the (k-1)-skeleton of a (n-1)-simplex
Sk   : (k : ℕ) → SST k → ℕ → Set
Sk→  : (k : ℕ) (X : SST k) {m n : ℕ} → (m →+ n) → Sk k X n → Sk k X m
Sk→∘ : (k : ℕ) (X : SST k) {n₁ n₂ n₃ : ℕ} (f : n₁ →+ n₂) (g : n₂ →+ n₃)
       → Sk→ k X (g ∘+ f) == Sk→ k X f ∘ Sk→ k X g

{- Need coherence: commutativity of the following diagram

                         Sk→∘(e, g ∘+ f)
       Sk→(g ∘+ f ∘+ e)  ===============  Sk→(e) ∘ Sk→(g ∘+ f)
                ∥                                ∥
Sk→∘(f ∘+ e, g) ∥                ∘               ∥ Sk→∘(f,g) |in-ctx [Sk→(e) ∘ -]
                ∥                                ∥
      Sk→(f ∘+ e) ∘ Sk→(g)  ==========  Sk→(e) ∘ Sk→(f) ∘ Sk→(g)
                   Sk→∘(e,f) |in-ctx [- ∘ Sk→(g)]
-}

Sk→∘-coh : (k : ℕ) (X : SST k)
           {n₁ n₂ n₃ n₄ : ℕ} (e : n₁ →+ n₂) (f : n₂ →+ n₃) (g : n₃ →+ n₄)
           → Sk→∘ k X e (g ∘+ f) ∙ ap (Sk→ k X e ∘_) (Sk→∘ k X f g)
             ==
             Sk→∘ k X (f ∘+ e) g ∙ ap (_∘ Sk→ k X g) (Sk→∘ k X e f)

SST O = ⊤₁
SST (S k) = Σ (SST k) λ X →
              Sk k X (S k) → Set

Sk O _ n = ⊤
Sk (S k) (X , Y) n = Σ (Sk k X n) λ x →
                       (f : (S k) →+ n) → Y (Sk→ k X f x)

Sk→ O _ _  x = x
Sk→ (S k) (X , Y) g (x , F) =
  (Sk→ k X g x , λ f → transport Y (app= (Sk→∘ k X f g) x) (F (g ∘+ f)))


Sk→∘ O X f g = idp
Sk→∘ (S k) (X , Y) {n₁} f g = λ= H where
  H : Sk→ (S k) (X , Y) (g ∘+ f)
      ∼ Sk→ (S k) (X , Y) f ∘ Sk→ (S k) (X , Y) g
  H (x , F) = pair= (app= (Sk→∘ k X f g) x) (
    from-transp (λ x' → (f' : S k →+ n₁) → Y (Sk→ k X f' x')) (app= (Sk→∘ k X f g) x) (

      transport (λ x' → (f' : S k →+ n₁) → Y (Sk→ k X f' x')) (app= (Sk→∘ k X f g) x)
        (λ e → transport Y (app= (Sk→∘ k X e (g ∘+ f)) x) (F ((g ∘+ f) ∘+ e)))

      =⟨ transp-λ (app= (Sk→∘ k X f g) x)
           (λ e → transport Y (app= (Sk→∘ k X e (g ∘+ f)) x) (F ((g ∘+ f) ∘+ e))) ⟩

      (λ e →
           transport (λ x' → Y (Sk→ k X e x')) (app= (Sk→∘ k X f g) x)
             (transport Y (app= (Sk→∘ k X e (g ∘+ f)) x) (F ((g ∘+ f) ∘+ e))))

      =⟨ λ= (λ e →

         transport (λ x' → Y (Sk→ k X e x')) (app= (Sk→∘ k X f g) x)
           (transport Y (app= (Sk→∘ k X e (g ∘+ f)) x) (F ((g ∘+ f) ∘+ e)))

         =⟨ transp-ap Y (Sk→ k X e) (app= (Sk→∘ k X f g) x)
            |in-ctx (λ tr →
              tr (transport Y (app= (Sk→∘ k X e (g ∘+ f)) x) (F ((g ∘+ f) ∘+ e)))) ⟩

         transport Y (ap (Sk→ k X e) (app= (Sk→∘ k X f g) x))
           (transport Y (app= (Sk→∘ k X e (g ∘+ f)) x) (F ((g ∘+ f) ∘+ e)))

         =⟨ ! (transp-∙ (app= (Sk→∘ k X e (g ∘+ f)) x)
                        (ap (Sk→ k X e) (app= (Sk→∘ k X f g) x))
                        (F ((g ∘+ f) ∘+ e))) ⟩

         transport Y
           (app= (Sk→∘ k X e (g ∘+ f)) x ∙ (ap (Sk→ k X e) (app= (Sk→∘ k X f g) x)))
           (F ((g ∘+ f) ∘+ e))

         =⟨ (
            ap (λ u → u x) (Sk→∘ k X e (g ∘+ f)) ∙ ap (Sk→ k X e) (app= (Sk→∘ k X f g) x)

            =⟨ ! (ap-app-l (Sk→ k X e) (Sk→∘ k X f g) x)
               |in-ctx (ap (λ u → u x) (Sk→∘ k X e (g ∘+ f)) ∙_) ⟩

            ap (λ u → u x) (Sk→∘ k X e (g ∘+ f)) ∙ ap (λ u → u x) (ap (Sk→ k X e ∘_) (Sk→∘ k X f g))

            =⟨ ap∙ap (Sk→∘ k X e (g ∘+ f)) (ap (Sk→ k X e ∘_) (Sk→∘ k X f g))
                     (Sk→∘ k X (f ∘+ e) g) (ap (_∘ Sk→ k X g) (Sk→∘ k X e f))
                     x (Sk→∘-coh k X e f g) ⟩

            ap (λ u → u x) (Sk→∘ k X (f ∘+ e) g) ∙ ap (λ u → u x) (ap (_∘ Sk→ k X g) (Sk→∘ k X e f))

            =⟨ ap-app-r (Sk→ k X g) (Sk→∘ k X e f) x
               |in-ctx (ap (λ u → u x) (Sk→∘ k X (f ∘+ e) g) ∙_) ⟩

            ap (λ u → u x) (Sk→∘ k X (f ∘+ e) g) ∙ app= (Sk→∘ k X e f) (Sk→ k X g x)

            =∎
            ) |in-ctx (λ p → transport Y p (F (g ∘+ f ∘+ e))) ⟩

         transport Y
           (app= (Sk→∘ k X (f ∘+ e) g) x ∙ (app= (Sk→∘ k X e f) (Sk→ k X g x)))
           (F (g ∘+ f ∘+ e))

         =⟨ transp-∙ (app= (Sk→∘ k X (f ∘+ e) g) x) (app= (Sk→∘ k X e f) (Sk→ k X g x))
                     (F (g ∘+ f ∘+ e)) ⟩

         transport Y (app= (Sk→∘ k X e f) (Sk→ k X g x))
           (transport Y (app= (Sk→∘ k X (f ∘+ e) g) x) (F (g ∘+ f ∘+ e)))

         =∎) ⟩

      (λ e →
           transport Y (app= (Sk→∘ k X e f) (Sk→ k X g x))
             (transport Y (app= (Sk→∘ k X (f ∘+ e) g) x) (F (g ∘+ f ∘+ e))))
      =∎
      )
    )

Sk→∘-coh O X e f g = idp
Sk→∘-coh (S k) (X , Y) e f g = {!!}
