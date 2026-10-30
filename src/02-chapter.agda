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

data _≡_ {ℓ} {A : Set ℓ} : (a b : A) → Set ℓ where
  refl : (a : A) → a ≡ a

symm : {A : Set} {a b : A} → a ≡ b → b ≡ a
symm (refl a) = refl a

trans : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans e1 (refl a) = e1

p*refl=p : {A : Set} {a b : A} → (p : a ≡ b) → trans p (refl b) ≡ p
p*refl=p (refl a) = refl (refl a)

refl*p=p : {A : Set} {a b : A} → (p : a ≡ b) → trans (refl a) p ≡ p
refl*p=p (refl b) = refl (refl b)

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
ns f g h (refl x) = refl*p=p (h x)

-- Chapter 2.7 Identifying elements in members of families of types
_-lifted_≡_over_ : {A : Set} (Y : A → Set) {a a' : A} →
  Y a → Y a' → a ≡ a' → Set
Y -lifted y ≡ y' over (refl a) = y ≡ y'

const : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'} → A → B → A
const x _ = x

const-lifted-≡ :
  {A Z : Set}
  {a a' : A}
  {z z' : Z}
  (p : a ≡ a') →
  ((const Z) -lifted z ≡ z' over p) ≡ (z ≡ z')
const-lifted-≡ (refl a) = refl _

po :
  {A : Set} {a a' : A} (p : a ≡ a')
  {Y : A → Set} (y : Y a) (y' : Y a') →
  (Y -lifted y ≡ y' over p) ≡ (trp Y p y ≡ y')
po (refl a) y y' = refl (y ≡ y')


trans-over : ∀ {A} {Y}
  {a a' a'' : A}
  {y1 y2 y3}
  {p : a ≡ a'} {p' : a' ≡ a''} →
  Y -lifted y1 ≡ y2 over p  →
  Y -lifted y2 ≡ y3 over p' →
  Y -lifted y1 ≡ y3 over (trans p p')
trans-over {p = p} {p' = (refl a)} q (refl y2) = q

symm-over : ∀ {A Y}
  {a a' : A}
  {y y'}
  {p : a ≡ a'} →
  (Y -lifted y  ≡ y' over p) →
  (Y -lifted y' ≡ y over (symm p))
symm-over {p = refl a} q = symm q

q*refl=q-over : ∀ {A Y}
  {a a' : A}
  {y y'}
  (p : a ≡ a') →
  (q : Y -lifted y  ≡ y' over p) →
  ((λ p0 → Y -lifted y ≡ y' over p0) -lifted
   (trans-over q (refl y')) ≡ q over p*refl=p p)
q*refl=q-over (refl a) q = refl q

refl*q=q-over : ∀ {A Y}
  {a a' : A}
  {y y'}
  (p : a ≡ a') →
  (q : Y -lifted y  ≡ y' over p) →
  ((λ p0 → Y -lifted y ≡ y' over p0) -lifted
   (trans-over (refl y) q) ≡ q over refl*p=p p)
refl*q=q-over (refl a) (refl y) = refl (refl y)

*-assoc-over :
  ∀ {A : Set} {Y : A → Set} {a1 a2 a3 a4 : A}
  {p1 : a1 ≡ a2} {p2 : a2 ≡ a3} {p3 : a3 ≡ a4}
  {y1 y2 y3 y4} →
  (q1 : Y -lifted y1 ≡ y2 over p1) →
  (q2 : Y -lifted y2 ≡ y3 over p2) →
  (q3 : Y -lifted y3 ≡ y4 over p3) →
  ((λ p0 → Y -lifted y1 ≡ y4 over p0) -lifted
  trans-over q1 (trans-over q2 q3) ≡ trans-over (trans-over q1 q2) q3
  over (*-assoc p1 p2 p3) )
*-assoc-over {p3 = refl a3} q1 q2 (refl y3) = refl (trans-over q1 q2)


l-inv-over : ∀ {A Y} {a a' : A} {y y'}
  {p : a ≡ a'}
  (q : Y -lifted y ≡ y' over p) →
  ((λ p0 → Y -lifted y' ≡ y' over p0) -lifted
   trans-over (symm-over q) q ≡ (refl y') over l-inv p)
l-inv-over {p = refl a} (refl y) = refl (refl y)

r-inv-over : ∀ {A Y} {a a' : A} {y y'}
  {p : a ≡ a'}
  (q : Y -lifted y ≡ y' over p) →
  ((λ p0 → Y -lifted y ≡ y over p0) -lifted
   trans-over q (symm-over q) ≡ (refl y) over r-inv p)
r-inv-over {p = refl a} (refl y) = refl (refl y)

inv-over : ∀ {A Y} {a a' : A} {y y'}
  {p : a ≡ a'}
  (q : Y -lifted y ≡ y' over p) →
  ((λ p0 → Y -lifted y ≡ y' over p0) -lifted
  (symm-over (symm-over q)) ≡ q over inv p)
inv-over {p = refl a} (refl y) = refl (refl y)

apd : ∀ {A B}
  (f : (a : A) → B a)
  {a a' : A}
  (p : a ≡ a') →
  B -lifted f a ≡ f a' over p
apd f (refl a) = refl (f a)

apap : ∀ {X Y} {Z : Set}
  (g : (x : X) → Y x → Z)
  {x x'} {y y'}
  (p : x ≡ x')
  (q : Y -lifted y ≡ y' over p) →
  (g x y ≡ g x' y')
apap g (refl x) (refl y) = refl (g x y)

apap=ap : ∀ {X : Set} {Y : X → Set} {Z : Set}
  (g : (x : X) → Y x → Z)
  {x} {y y' : Y x}
  (p : y ≡ y') →
  apap g (refl x) p ≡ ap (g x) p
apap=ap g {x} (refl y) = refl (refl (g x y))
