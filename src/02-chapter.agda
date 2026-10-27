data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

compose : {A B C : Set} → (B → C) → (A → B) → (A → C)
compose g f a = g (f a)

iter : {A : Set} → ℕ → (A → A) → (A → A)
iter zero f = λ x → x
iter (succ n) f = compose f (iter n f)

plus : ℕ → ℕ → ℕ
plus x y = iter x succ y

mul : ℕ → ℕ → ℕ
mul x y = iter x (plus y) zero

fact : ℕ → ℕ
fact zero = succ zero
fact (succ n) = mul (succ n) (fact n)

data _≡_ {A : Set} : (a b : A) → Set where
  refl : (a : A) → a ≡ a

symm : {A : Set} {a b : A} → a ≡ b → b ≡ a
symm (refl a) = refl a

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans e1 (refl a) = e1

p*refl=p : {A : Set} {a b : A} → (p : a ≡ b) → trans p (refl b) ≡ p
p*refl=p (refl a) = refl (refl a)

p=p*refl : {A : Set} {a b : A} → (p : a ≡ b) → trans (refl a) p ≡ p
p=p*refl (refl b) = refl (refl b)

*-assoc : {A : Set} {a b c d : A}
  → (p : a ≡ b)
  → (q : b ≡ c)
  → (r : c ≡ d)
  → trans p (trans q r) ≡ trans (trans p q) r
*-assoc p q (refl c) = refl (trans p q)

l-inv : {A : Set} {a b : A} → (p : a ≡ b) → trans (symm p) p ≡ refl b
l-inv (refl a) = refl (refl a)

r-inv : {A : Set} {a b : A} → (p : a ≡ b) → trans p (symm p) ≡ refl a
r-inv (refl a) = refl (refl a)

inv : {A : Set} {a b : A} → (p : a ≡ b) → symm (symm p) ≡ p
inv (refl a) = refl (refl a)

trp : {A : Set} {a b : A} (T : A → Set) → a ≡ b → T a → T b
trp T (refl a) t = t

trp-comm : {A : Set} {a b c : A} →
  (T : A → Set) →
  (e₁ : a ≡ b) →
  (e₂ : b ≡ c) →
  trp T (trans e₁ e₂) ≡ compose (trp T e₂) (trp T e₁)
trp-comm T e₁ (refl b) = refl (trp T e₁)

const-trp : {X Y : Set} {a b : X}
  (p : a ≡ b) →
  trp (λ _ → Y) p ≡ (λ x → x)
const-trp (refl a) = refl _

ap : {X Y : Set} {x x' : X}
  (f : X → Y)  → x ≡ x' → f x ≡ f x'
ap f (refl a) = refl (f a)

ap-trans-comm : {X Y : Set} (f : X → Y) {x x' x'' : X}
  (p : x ≡ x') (p' : x' ≡ x'') →
  ap f (trans p p') ≡ trans (ap f p) (ap f p')
ap-trans-comm f p (refl a) = refl (ap f p)

ap-symm-comm : {X Y : Set} (f : X → Y) {x x' : X}
  (p : x ≡ x') →
  ap f (symm p) ≡ symm (ap f p)
ap-symm-comm f (refl a) = refl _

trp-ap : {A X : Set} {f : A → X} {T : X → Set}
  {a a' : A} (p : a ≡ a') →
  trp (λ a → T (f a)) p ≡ trp T (ap f p)
trp-ap (refl a) = refl _

ptw : {A B : Set} {f g : A → B} →
  (p : f ≡ g) →
  (∀ x → f x ≡ g x)
ptw (refl f) x = refl (f x)

ns : {X Y : Set} {x x' : X} →
  (f g : X → Y) →
  (h : ∀ x → f x ≡ g x)
  (p : x ≡ x') →
  trans (ap f p) (h x') ≡ trans (h x) (ap g p)
ns f g h (refl x) = p=p*refl (h x)

