{-
 - Exercises from Ulf Norell's Agda tutorial.
 - Solved by Artyom Shalkhakov, artyom DOT shalkhakov AT gmail DOT com.
 - Read at your own peril (this will spoil all the fun).
 - Date: September 2012.
 -}
module Main0 where

data Bool : Set where
  true : Bool
  false : Bool

¬_ : Bool → Bool
¬ true = false
¬ false = false

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

_+_ : Nat → Nat → Nat
zero + m = m
suc n + m = suc (n + m)

_*_ : Nat → Nat → Nat
zero * m = zero
suc n * m = m + n * m

_∨_ : Bool → Bool → Bool
true ∨ x = x
false ∨ _ = false

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

infixl 60 _*_
infixl 40 _+_
infixr 20 _∨_
infix 5 if_then_else_

-- infixr 40 _∷_
data [_] (α : Set) : Set where
  [] : [ α ]
  _∷_ : α → [ α ] → [ α ]

identity : (α : Set) → α → α
identity α x = x

zero' : Nat
zero' = identity Nat zero

apply : (α : Set) → (β : α → Set) → ((x : α) → β x) → (a : α) → β a
apply α β f a = f a

-- identity₂: (α : Set) → α → α
-- identity₂= λ α x → x

-- function composition
_◦_ : {α : Set} {β : α → Set} {γ : (x : α) → β x → Set}
      (f : {x : α} (y : β x) → γ x y) (g : (x : α) → β x)
      (x : α) → γ x (g x)
(f ◦ g) x = f (g x)

plus-two = suc ◦ suc

map : {α β : Set} → (α → β) → [ α ] → [ β ]
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_++_ : {α : Set} → [ α ] → [ α ] → [ α ]
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Vec (α : Set) : Nat -> Set where
  [] : Vec α zero
  _∷_ : {n : Nat} → α → Vec α n → Vec α (suc n)

head : {α : Set} {n : Nat} → Vec α (suc n) → α
head (x ∷ xs) = x

tail : {α : Set} {n : Nat} → Vec α (suc n) → Vec α n
tail (x ∷ xs) = xs

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

magic : {α : Set} → Fin zero → α
magic ()

data Empty : Set where
  empty : Fin zero → Empty

magic′ : {α : Set} → Empty → α
magic′ (empty ())

_!_ : {n : Nat}{α : Set} → Vec α n → Fin n → α
[] ! ()
(x ∷ xs) ! fzero = x
(x ∷ xs) ! (fsuc i) = xs ! i

tabulate : {n : Nat}{α : Set} → (Fin n → α) → Vec α n
tabulate {zero} f = []
tabulate {suc n} f = f fzero ∷ tabulate (f ◦ fsuc)

-- Propositions

data ⊥ : Set where
record ⊤ : Set where

trivial : ⊤
trivial = _

is⊤ : Bool → Set
is⊤ true = ⊤
is⊤ false = ⊥

_<_ : Nat -> Nat -> Bool
_ < zero = false
zero < suc n = true
suc m < suc n = m < n

length : {α : Set} → [ α ] → Nat
length [] = zero
length (_ ∷ xs) = suc (length xs)

lookup : {α : Set}(xs : [ α ])(n : Nat) → is⊤ (n < length xs) → α
lookup [] n ()
lookup (x ∷ xs) zero p = x
lookup (x ∷ xs) (suc n) p = lookup xs n p

data _≡_ {α : Set}(x : α) : α → Set where
  refl : x ≡ x

data _≤_ : Nat → Nat → Set where
  leq-zero : {n : Nat} → zero ≤ n
  leq-suc : {m n : Nat} → m ≤ n → suc m ≤ suc n

leq-refl : (n : Nat) → n ≤ n
leq-refl zero = leq-zero
leq-refl (suc m) = leq-suc (leq-refl m)

eq-step1 : {n m : Nat} → n ≡ m → suc n ≡ suc m
eq-step1 refl = refl

leq-curious : {n m : Nat} → n ≤ m → m ≤ n → m ≡ n
leq-curious leq-zero leq-zero = refl
leq-curious (leq-suc n′) (leq-suc m′) = eq-step1 (leq-curious n′ m′)

leq-trans : {l m n : Nat} → l ≤ m → m ≤ n → l ≤ n
leq-trans leq-zero _ = leq-zero
leq-trans (leq-suc p) (leq-suc q) = leq-suc (leq-trans p q)

min : Nat → Nat → Nat
min x y with x < y
min x y | true = x
min x y | false = y

data _≠_ : Nat → Nat → Set where
  z≠s : {n : Nat} → zero ≠ suc n
  s≠z : {n : Nat} → suc n ≠ zero
  s≠s : {m n : Nat} → m ≠ n → suc m ≠ suc n
data Equal? (n m : Nat) : Set where
  eq : n ≡ m → Equal? n m
  neq : n ≠ m → Equal? n m

equal? : (n m : Nat) → Equal? n m
equal? zero zero = eq refl
equal? zero (suc m) = neq z≠s
equal? (suc n) zero = neq s≠z
equal? (suc n) (suc m) with equal? n m
equal? (suc n) (suc .n) | eq refl = eq refl
equal? (suc n) (suc m) | neq p = neq (s≠s p)

lt-implies-lte : (x y : Nat) → (x < y) ≡ true → x ≤ y
lt-implies-lte _ zero ()
lt-implies-lte zero (suc n) refl = leq-zero
lt-implies-lte (suc m) (suc n) pf = leq-suc (lt-implies-lte m n pf)

-- FIXME: how to prove?
data disj (A B : Set) : Set where
  disj1 : A → disj A B
  disj2 : B → disj A B

data conj (A B : Set) : Set where
  _,_ : A → B → conj A B

min-thm0 : (x y z : Nat) → z ≡ min x y → disj (z ≡ x) (z ≡ y)
min-thm0 x y z pf with x < y
min-thm0 x y .x refl | true = disj1 refl
min-thm0 x y .y refl | false = disj2 refl

{-
min-thm1 : (x y z : Nat) → z ≡ min x y → conj (z ≤ x) (z ≤ y)
min-thm1 x y z pf with x < y
min-thm1 x y .x refl | true = leq-refl x , lt-implies-lte x y refl
min-thm1 x y .y refl | false = lt-implies-lte y x false , leq-refl y
-}

max : Nat → Nat → Nat
max x y with y < x
max x y | true = x
max x y | false = y

infix 20 _⊆_
data _⊆_ {A : Set} : [ A ] → [ A ] → Set where
  stop : [] ⊆ []
  drop : forall {xs y ys} → xs ⊆ ys → xs ⊆ y ∷ ys
  keep : forall {x xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys

filter : {α : Set} → (α → Bool) → [ α ] → [ α ]
filter p [] = []
filter p (x ∷ xs) with p x
... | true = x ∷ filter p xs
... | false = filter p xs

lem-filter : {α : Set} (p : α → Bool) (xs : [ α ]) → filter p xs ⊆ xs
lem-filter p [] = stop
lem-filter p (x ∷ xs) with p x
... | true = keep (lem-filter p xs)
... | false = drop (lem-filter p xs)

module Option where
  data option (α : Set) : Set where
    none : option α
    some : α → option α
  elim : {α β : Set} → β → (α → β) → option α → β
  elim z f none = z
  elim z f (some x) = f x
module Sort (α : Set) (_<_ : α → α → Bool) where
  insert : α → [ α ] → [ α ]
  insert y [] = y ∷ []
  insert y (x ∷ xs) with x < y
  ... | true = x ∷ insert y xs
  ... | false = y ∷ x ∷ xs

  sort : [ α ] → [ α ]
  sort [] = []
  sort (x ∷ xs) = insert x (sort xs)
module SortNat = Sort Nat _<_
open Sort Nat _<_ renaming (insert to insertℕ; sort to sortℕ)

record Point : Set where
  field x : Nat
        y : Nat

mkPoint : Nat → Nat → Point
mkPoint a b = record{ x = a; y = b}

abs² : Point → Nat
abs² p = let open Point p in x * x + y * y

record Monad (μ : Set → Set) : Set1 where
  field
    return : {α : Set} → α → μ α
    _>>=_ : {α β : Set} → μ α → (α → μ β) → μ β

  -- state monad laws?

  mapM : {α β : Set} → (α → μ β) → [ α ] → μ [ β ]
  mapM f [] = return []
  mapM f (x ∷ xs) = f x  >>= λ y →
                    mapM f xs >>= λ ys →
                    return (y ∷ ys)

-- Exercises
Matrix : Set → Nat → Nat → Set
Matrix A n m = Vec (Vec A n) m

vec : {n : Nat} {α : Set} → α → Vec α n
vec {zero} x = []
vec {suc n} x = x ∷ vec {n} x

infixl 90 _$_
_$_ : {n : Nat}{α β : Set} → Vec (α → β) n → Vec α n → Vec β n
[] $ [] = []
(f ∷ fs) $ (x ∷ xs) = f x ∷ (fs $ xs)

-- transpose : forall {α n m} → Matrix α n m → Matrix α m n
-- transpose xss = {! !}
-- transposition of matrices in terms of vec and $?
-- x1 x2 --> x1 y1 z1
-- y1 y2 --> x2 y2 z2
-- z1 z2 -->

-- [head [x1, x2], head [y1, y2], head [z1, z2]]
-- -->
-- [x1, y1, z1]
--   Vec (Vec α (suc m)) n → Vec α n
-- -->
--   also, take tails
--   [[x2], [y2], [z2]]
--   (vec {m} tail) $ xss
-- [[x1, y1, z1], [x2, y2, z2]]
--   applied "head" to every list, putting results into one list
--   repeat the same with tails
-- (vec {m} head) $ xss

heads : forall {α n m} → Matrix α (suc n) m → Vec α m
heads xxs = (vec head) $ xxs

tails : forall {α n m} → Matrix α (suc n) m → Vec (Vec α n) m
tails xxs = (vec tail) $ xxs

transpose : forall {α n m} → Matrix α n m → Matrix α m n
transpose {α}{zero} xxs = []
transpose {α}{suc n} xxs = ((vec head) $ xxs) ∷ transpose{α}{n} ((vec tail) $ xxs)

_!_,_ : {α : Set}{m n : Nat} → (A : Matrix α m n) → (i : Fin n) → (j : Fin m) → α
A ! i , j = (A ! i) ! j

-- TODO: prove correctness of transpose:
-- A' = transpose A where

fone = fzero {zero}

-- Vec (Vec α (suc zero)) (suc zero)
transpose-correct00 : {α : Set} → (A : Matrix α zero zero) → A ≡ transpose A
transpose-correct00 A with transpose A
transpose-correct00 [] | [] = refl

transpose-correct01 : {α : Set} → (A : Matrix α (suc zero) (suc zero)) → (A ! fzero , fzero) ≡ (transpose A ! fzero , fzero)
transpose-correct01{α} ((x ∷ []) ∷ []) with transpose-correct00{α} []
... | refl = refl

rewrite-eq : {A : Set}{a b : A}{P : A → Set} → a ≡ b → P a → P b
rewrite-eq refl p = p

-- exercise 2.2: prove that _!_ and tabulate are inverses
-- (a)
lem-!-tab : forall {A n} (f : Fin n → A) → (i : Fin n) → (tabulate f ! i) ≡ f i
lem-!-tab f fzero = refl
lem-!-tab f (fsuc j) = lem-!-tab (f ◦ fsuc) j
-- (b)
lem-tab-!-one : forall {A n} (x : A) (xs : Vec A n) → x ∷ (tabulate (_!_ xs)) ≡ tabulate (_!_ (x ∷ xs))
lem-tab-!-one x [] = refl
lem-tab-!-one x (y ∷ xs) with lem-tab-!-one y xs
lem-tab-!-one x (y ∷ xs) | refl = refl

lem-tab-! : forall {A n} (xs : Vec A n) → tabulate (_!_ xs) ≡ xs
lem-tab-! {A}{zero} [] = refl
lem-tab-! {A}{suc n} (x ∷ xs) with (lem-tab-!-one x xs)
... | refl = suc-inj (lem-tab-! xs) where
  suc-inj : {A : Set} {n : Nat} {x : A} {xs ys : Vec A n} → xs ≡ ys → (_≡_{Vec A (suc n)} (x ∷ xs) (x ∷ ys))
  suc-inj {x = x} {xs = xs} {ys = .xs} refl = refl   
{-
tabulate (_!_ []) ≡ [] -- by first clause
we want to show (tabulate (_!_ (x ∷ [])) ≡ x ∷ []):
  evaluating LHS:
    tabulate (_!_ (x ∷ [])) ==> (_!_ (x ∷ [])) fzero ∷ tabulate ((_!_ (x ∷ [])) ◦ fsuc)
    where (_!_ (x ∷ [])) fzero ==> x
          tabulate ((_!_ (x ∷ [])) ◦ fsuc) ==> []
    and thus we have LHS ≡ RHS
now, abstracting out the tail [], we get:
- want to show (tabulate (_!_ (x ∷ xs)) ≡ x ∷ xs)
  - inductive hypothesis: (tabulate (_!_ xs) ≡ xs)
      pf : (tabulate (_!_ xs) ≡ xs) = <obtain with the recursive call>
  - cons x onto both sides: x ∷ (tabulate (_!_ xs)) ≡ x ∷ xs
      suc-inj : {A : Set} {n : Nat} {x : A} {xs ys : Vec A n} → xs ≡ ys → (_≡_{Vec A (suc n)} (x ∷ xs) (x ∷ ys))
      pf1 = suc-inj pf
  - want: x ∷ (tabulate (_!_ xs)) ≡ tabulate (_!_ (x ∷ xs))
      tabulate (_!_ (x ∷ xs)) ==> (_!_ (x ∷ xs)) fzero ∷ tabulate ((_!_ (x ∷ xs)) ◦ fsuc)
      where (_!_ (x ∷ xs)) fzero ==> x
      reflexivity
      lem-tab-!-one
-} 

-- 2.3
-- (a) prove that _⊆_ is reflexive
⊆-refl : {A : Set}{xs : [ A ]} → xs ⊆ xs
⊆-refl{A} {[]} = stop
⊆-refl{A} {x ∷ xs'} = keep (⊆-refl {A}{xs'})
-- (b) prove that _⊆_ is transitive
⊆-emp : {A : Set} (xs : [ A ]) → [] ⊆ xs
⊆-emp [] = stop
⊆-emp (_ ∷ xs) = drop (⊆-emp xs)

⊆-drop : {A : Set}{xs : [ A ]}{ys : [ A ]}{x : A} → x ∷ xs ⊆ ys → xs ⊆ ys
⊆-drop (keep p) = drop p
⊆-drop (drop p) = drop (⊆-drop p)

⊆-trans : {A : Set}{xs ys zs : [ A ]} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans .{xs = []} {zs = zs} stop _ = ⊆-emp zs
⊆-trans (drop pf′) pf1 = ⊆-trans pf′ (⊆-drop pf1)
⊆-trans (keep pf′) (keep pf2) = keep (⊆-trans pf′ pf2)
  -- pf′ : xs' ⊆ ys'
  -- pf1 = keep pf2 : x ∷ ys' ⊆ x ∷ zs' where zs ≡ x ∷ zs':
  --   pf2 : ys' ⊆ zs'
  --   pf3 = ⊆-trans pf′ pf2 : xs' ⊆ zs'
  --   keep pf3 : x ∷ xs' ⊆ x ∷ zs'
⊆-trans (keep pf′) (drop pf2) = drop (⊆-trans (keep pf′) pf2)
  -- keep pf′ : x ∷ xs' ⊆ x ∷ ys'
  -- pf1 = drop pf2 : x ∷ ys' ⊆ z ∷ zs'
  -- pf2 : x ∷ ys' ⊆ zs'
  -- ⊆-trans (keep pf′) pf2) : x ∷ xs' ⊆ zs'
  -- drop (⊆-trans (keep pf′) pf2) : x ∷ xs' ⊆ z ∷ zs'

infixr 30 _∷_
data SubList {A : Set} : [ A ] → Set where
  [] : SubList []
  _∷_ : forall x {xs} → SubList xs → SubList (x ∷ xs)
  skip : forall {x xs} → SubList xs → SubList (x ∷ xs)

-- (b)
-- extract the list corresponding to a sublist
forget : {A : Set}{xs : [ A ]} → SubList xs → [ A ]
forget [] = []
forget (x ∷ xs) = x ∷ forget xs
forget {xs = x ∷ xs′} (skip ys) = x ∷ forget ys
-- (c)
-- prove that SubList is a sublist in a sense of _⊆_
lem-forget : {A : Set}{xs : [ A ]}(zs : SubList xs) → forget zs ⊆ xs
lem-forget [] = stop
lem-forget (x ∷ xs) = keep (lem-forget xs)
lem-forget (skip xs) = keep (lem-forget xs)
-- (d)
-- define [filter'] which satisfies SubList property by construction
filter' : {A : Set} → (A → Bool) → (xs : [ A ]) → SubList xs
filter' p [] = []
filter' p (x ∷ xs) with p x
... | true = x ∷ filter' p xs
... | false = skip (filter' p xs)
-- (e)
-- here, "complement of a sublist S" means: another sublist R which
-- only contains elements not in S
complement : {A : Set}{xs : [ A ]} → SubList xs → SubList xs
complement {xs = []} [] = []
complement (x ∷ xs) = skip (complement xs)
complement {xs = x ∷ xs'} (skip ys) = x ∷ complement ys
-- (f)
-- compute all sublists of a given list
-- [] → []
-- [1,2] → [[1], [2], [1,2]]
-- [1,2,3] → [[1], [2], [1,2], [1,3], [2,3], [1,2,3]]
-- etc.
sl-map : {α : Set}{x : α}{xs : [ α ]} → [ SubList xs ] → [ SubList (x ∷ xs) ]
sl-map [] = []
sl-map {x = x} (y ∷ ys) = (x ∷ y) ∷ sl-map ys

sublists : {A : Set}{xs : [ A ]} → [ SubList xs ]
sublists {xs = []} = []
sublists {xs = (x ∷ xs')} with sublists {xs = xs'}
... | xss = map skip xss ++ sl-map {x = x} xss
