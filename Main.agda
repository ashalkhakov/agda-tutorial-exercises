{-
 - Exercises from Ulf Norell's Agda tutorial.
 - Solved by Artyom Shalkhakov, artyom DOT shalkhakov AT gmail DOT com.
 - Read at your own peril (this will spoil all the fun).
 - Date: September 2012.
 -}
module Main where

open import Data.Nat

data Parity : ℕ → Set where
  even : (k : ℕ) → Parity (k * 2)
  odd : (k : ℕ) → Parity (1 + k * 2)

parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc n) with parity n
parity (suc .(k * 2)) | even k = odd k
parity (suc .(1 + (k * 2))) | odd k = even (suc k)

half : ℕ → ℕ
half n with parity n
half .(k * 2) | even k = k
half .(1 + k * 2) | odd k = k

open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Unit
open import Data.List
open import Data.Bool

infixr 30 _:all:_
data All {A : Set}(P : A → Set) : List A → Set where
  all[] : All P []
  _:all:_ : forall {x xs} → P x → All P xs → All P (x ∷ xs)

satisfies : {A : Set} → (A → Bool) → A → Set
satisfies p x = T (p x)

data Sat {A : Set}(P : A → Bool) : A → Set where
  sat : (x : A)(pf : P x ≡ true) → Sat P x

data Inspect {A : Set}(x : A) : Set where
  it : (y : A) → x ≡ y → Inspect x
insp : {A : Set}(x : A) → Inspect x
insp x = it x refl

-- the current standard lib defines [filter] via a more general
-- function [gfilter], so we define our own function instead
filter1 : {A : Set} → (A → Bool) → List A → List A
filter1 p [] = []
filter1 p (x ∷ xs) with (insp (p x))
... | it true prf = x ∷ (filter1 p xs)
... | it false prf = filter1 p xs

-- exercise: all elements of the result of [filter] satisfy the predicate
-- FIXME:
--  1. due to [gfilter] (see above), can't prove to typechecker that two function bodies
--    are equal; moreover, if I don't use [Inspect] in my definition of [filter],
--    then I get a type error, something to the effect that
--      x ∷ (filter1 p xs')
--    and
--      x ∷ (filter1 p xs') | p x
--    are not equal
-- 2. is my definition of [Sat] correct? also, isn't it related to the existential quantifier?
lem-filter : {A : Set}{p : A → Bool}(xs : List A) →  All (Sat p) (filter1 p xs)
lem-filter [] = all[]
lem-filter{p = p} (x ∷ xs′) with insp (p x)
... | it true pf = sat x pf :all: (lem-filter xs′)
... | it false _ = lem-filter xs′

trueIsTrue : {x : Bool} → x ≡ true → T x
trueIsTrue refl = _

NT : (x : Bool) → Set
NT x = T (not x)
falseIsFalse : {x : Bool} → x ≡ false → NT x
falseIsFalse refl = _

data Find {A : Set}(p : A → Bool) : List A → Set where
  found : (xs : List A)(y : A) → satisfies p y → (ys : List A) → Find p (xs ++ y ∷ ys)
  not-found : forall {xs} → All (satisfies (not ∘ p)) xs → Find p xs

find : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
find p [] = not-found all[]
find p (x ∷ xs) with insp (p x)
... | it true prf = found [] x (trueIsTrue prf) xs
... | it false prf with find p xs
find p (x ∷ ._) | it false _ | found xs y py ys =
  found (x ∷ xs) y py ys
find p (x ∷ xs) | it false prf | not-found npxs =
  not-found (falseIsFalse prf :all: npxs)

-- what does it mean for an element to occur in a list?
data _∈_ {A : Set}(x : A) : List A → Set where
  -- x is the head of a list
  hd : forall {xs} → x ∈ (x ∷ xs)
  -- if x occurs in xs then it also occurs in y ∷ xs
  tl : forall {y xs} → x ∈ xs → x ∈ (y ∷ xs)

index : forall {A}{x : A}{xs} → x ∈ xs → ℕ
index hd = zero
index (tl p) = suc (index p)

data Lookup {A : Set}(xs : List A) : ℕ → Set where
  inside : (x : A)(p : x ∈ xs) → Lookup xs (index p)
  outside : (m : ℕ) → Lookup xs (length xs + m)

_!_ : {A : Set}(xs : List A)(n : ℕ) → Lookup xs n
[] ! n = outside n
(x ∷ xs) ! zero = inside x hd
(x ∷ xs) ! suc n with xs ! n
(x ∷ xs) ! suc .(index p)       | inside y p = inside y (tl p)
(x ∷ xs) ! suc .(length xs + n) | outside n = outside n

--
-- universes
--
data False : Set where {- no constructors -}
record True : Set where {- one implicit constructor -}

module Universes where
  data bool : Set where
    true : bool
    false : bool

  isTrue : bool → Set
  isTrue true = True
  isTrue false = False

  -- infix 30 bnot_
  --infixr 25 _and_

  bnot : bool → bool
  bnot true = false
  bnot false = true

  _band_ : bool → bool → bool
  true band x = x
  false band _ = false

  notNotId : (a : bool) → isTrue (bnot (bnot a)) → isTrue a
  notNotId true p = p
  notNotId false ()

  andIntro : (a b : bool) → isTrue a → isTrue b → isTrue (a band b)
  andIntro true _ _ p = p
  andIntro false _ () _

-- universes for generic programming
module GenericProgramming where
  data Functor : Set₁ where
    |Id| : Functor
    |K| : Set → Functor
    _|+|_ : Functor → Functor → Functor
    _|×|_ : Functor → Functor → Functor

  data _⊹_ (A B : Set) : Set where
    inl : A → A ⊹ B
    inr : B → A ⊹ B

  data _×_ (A B : Set) : Set where
    _,_ : A → B → A × B

  infixr 50 _|+|_ _⊹_
  infixr 60 _|×|_ _×_

  ⟦_⟧ : Functor → Set → Set
  ⟦ |Id| ⟧ X = X
  ⟦ |K| A ⟧ X = A
  ⟦ F |+| G ⟧ X = ⟦ F ⟧ X ⊹ ⟦ G ⟧ X
  ⟦ F |×| G ⟧ X = ⟦ F ⟧ X × ⟦ G ⟧ X

  fmap : (F : Functor){X Y : Set} → (X → Y) → ⟦ F ⟧ X → ⟦ F ⟧ Y
  fmap |Id| f x = f x
  fmap (|K| A) f c = c
  fmap (F |+| G) f (inl x) = inl (fmap F f x)
  fmap (F |+| G) f (inr x) = inr (fmap G f x)
  fmap (F |×| G) f (x , y) = fmap F f x , fmap G f y

  data μ_ (F : Functor) : Set where
    <_> : ⟦ F ⟧ (μ F) → μ F

  -- admittedly all this generic stuff goes way over my head;
  -- the cure would entail reading up on generic (polytypic)
  -- programming, as well as on some category theory. anyway,
  -- need some more experience with universes

  -- very interesting applications of universes. quote:
  -- "...XML schemas as codes for the types of well-formed XML documents"
  -- "...a universe of tables in a relational database, allowing us
  -- to make queries which are guaranteed to be well-typed"

-- exercises
module NatProp where
  -- 3.1 natural numbers
  data Compare : ℕ → ℕ → Set where
    less : forall {n} k → Compare n (n + suc k)
    more : forall {n} k → Compare (n + suc k) n
    same : forall {n} → Compare n n
  -- (a) define the view function:
  compare1 : (n m : ℕ) → Compare n m
  compare1 zero zero = same
  compare1 zero (suc n) = less n
  compare1 (suc n) zero = more n
  compare1 (suc n) (suc n') with compare1 n n'
  compare1 (suc n) (suc .(n + suc k)) | less k = less k
  compare1 (suc .(n + suc k)) (suc n) | more k = more k
  compare1 (suc .k) (suc .k) | same {k} = same

  -- (b) now use the view to compute the difference between two numbers
  difference1 : ℕ → ℕ → ℕ
  difference1 n m with compare1 n m
  difference1 .k .k | same {k} = zero
  difference1 .n .(n + suc k) | less {n} k = suc k
  difference1 .(n + suc k) .n | more {n} k = suc k

-- 3.2 type-checking STLC
module STLC where
  module AbSyn where -- abstract syntax
    -- types
    infixr 30 _⟶_
    data Type : Set where
      l : Type
      _⟶_ : Type → Type → Type

    -- raw terms (pre-terms)
    infixl 80 _app_
    data Raw : Set where
      var : ℕ → Raw
      _app_ : Raw → Raw → Raw
      lam : Type → Raw → Raw

    -- typing context
    Cxt = List Type

    -- typed terms (terms decorated with types);
    -- also our typing judgement
    data Term (Γ : Cxt) : Type → Set where
      var : forall {τ} → τ ∈ Γ → Term Γ τ
      _app_ : forall {σ τ} → Term Γ (σ ⟶ τ) → Term Γ σ → Term Γ τ
      lam : forall σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⟶ τ)

  module Check where -- type checker
    open AbSyn

    -- (a) define inequality on types and change
    -- comparison to include inequality proofs
    data _≠_ : Type → Type → Set where
      ≠l1 : forall {σ τ} → l ≠ (σ ⟶ τ)
      ≠l2 : forall {σ τ} → (σ ⟶ τ) ≠ l
      ≠a : forall {σ1 σ2 τ} → σ1 ≠ σ2 → σ1 ⟶ τ ≠ (σ2 ⟶ τ)
      ≠r : forall {σ τ1 τ2} → τ1 ≠ τ2 → σ ⟶ τ1 ≠ (σ ⟶ τ2)
      ≠t : forall {σ1 σ2 τ1 τ2} → σ1 ≠ τ1 → σ2 ≠ τ2 → (σ1 ⟶ σ2) ≠ (τ1 ⟶ τ2)

    data Equal? : Type → Type → Set where
      yes : forall {τ} → Equal? τ τ
      no : forall {σ τ} → σ ≠ τ → Equal? σ τ

    _=?=_ : (σ τ : Type) → Equal? σ τ
    l =?= l = yes
    l =?= y ⟶ y' = no ≠l1
    y ⟶ y' =?= l = no ≠l2
    y ⟶ y' =?= y0 ⟶ y1 with y =?= y0 | y' =?= y1
    y ⟶ y' =?= .y ⟶ .y' | yes   | yes   = yes
    y ⟶ y' =?= y0 ⟶ .y' | no p  | yes   = no (≠a p)
    y ⟶ y' =?= .y ⟶ y1  | yes   | no p  = no (≠r p)
    y ⟶ y' =?= y0 ⟶ y1  | no p1 | no p2 = no (≠t p1 p2)

    -- (b) define a type of ill-typed terms and change [infer]
    -- to return such a term upon failure
    data BadTerm (Γ : Cxt) : Set where
      var : {m n : ℕ} → length Γ + m ≡ n → BadTerm Γ
      _app0_ : BadTerm Γ → Raw → BadTerm Γ
      _app1_ : Term Γ l → Raw → BadTerm Γ
      _app2_ : {σ τ : Type} → Term Γ (σ ⟶ τ) → BadTerm Γ → BadTerm Γ
      app3 : {σ σ' τ : Type} → (σ ≠ σ') → Term Γ (σ ⟶ τ) → Term Γ σ' → BadTerm Γ
      lam : {σ : Type} → BadTerm (σ ∷ Γ) → BadTerm Γ

    erase : forall {Γ τ} → Term Γ τ → Raw
    erase (var y) = var (index y)
    erase (y app y') = erase y app erase y'
    erase (lam σ y) = lam σ (erase y)

    eraseBad : {Γ : Cxt} → BadTerm Γ → Raw
    eraseBad (var {m}{n} _) = var n
    eraseBad (b app0 e) = (eraseBad b) app e
    eraseBad (t app1 e) = (erase t) app e
    eraseBad (t app2 e) = (erase t) app (eraseBad e)
    eraseBad (app3 _ t1 t2) = (erase t1) app (erase t2)
    eraseBad (lam {σ} b) = lam σ (eraseBad b)

    data Infer (Γ : Cxt) : Raw → Set where
      ok : (τ : Type)(t : Term Γ τ) → Infer Γ (erase t)
      bad : (b : BadTerm Γ) → Infer Γ (eraseBad b)

    infer : (Γ : Cxt)(e : Raw) → Infer Γ e

    infer Γ (var n) with Γ ! n
    infer Γ (var .(length Γ + m)) | outside m = bad (var refl)
    infer Γ (var .(index x))      | inside σ x = ok σ (var x)

    infer Γ (e1 app e2) with infer Γ e1
    infer Γ (.(eraseBad b1) app e2) | bad b1 = bad (b1 app0 e2)
    infer Γ (.(erase t1) app e2)    | ok l t1 = bad (t1 app1 e2)
    infer Γ (.(erase t1) app e2)    | ok (σ ⟶ τ) t1
      with infer Γ e2
    infer Γ (.(erase t1) app .(eraseBad b2)) | ok (σ ⟶ τ) t1 | bad b2 =
      bad (t1 app2 b2)
    infer Γ (.(erase t1) app .(erase t2))    | ok (σ ⟶ τ) t1 | ok σ' t2
      with σ =?= σ'
    infer Γ (.(erase t1) app .(erase t2))    | ok (σ ⟶ τ) t1 | ok .σ t2 | yes  =
      ok τ (t1 app t2)
    infer Γ (.(erase t1) app .(erase t2))    | ok (σ ⟶ τ) t1 | ok σ' t2 | no p =
      bad (app3 p t1 t2)

    infer Γ (lam σ e) with infer (σ ∷ Γ) e
    infer Γ (lam σ .(erase t))     | ok τ t = ok (σ ⟶ τ) (lam σ t)
    infer Γ (lam σ .(eraseBad b))  | bad b  = bad (lam b)

-- 3.3 properties of list functions
module ListProps where
  -- (a)
  lemma-All-∈ : forall {A x xs}{P : A → Set} → All P xs → x ∈ xs → P x
  lemma-All-∈ {xs = []} p ()
  lemma-All-∈ (y :all: y') hd = y
  lemma-All-∈ (y' :all: y0) (tl p) = lemma-All-∈ y0 p

  -- (b)
  lem-filter-sound : {A : Set}(p : A → Bool)(xs : List A) →
      All (satisfies p) (filter p xs)
  lem-filter-sound p [] = all[]
  lem-filter-sound p (x ∷ xs) with insp (p x)
  lem-filter-sound p (x ∷ xs) | it y prf with p x | prf
  lem-filter-sound p (x ∷ xs) | it .true prf | true | refl =
    trueIsTrue prf :all: lem-filter-sound p xs
  lem-filter-sound p (x ∷ xs) | it .false prf | false | refl =
    lem-filter-sound p xs
  -- (c)
  lem-filter-complete : {A : Set}(p : A → Bool)(x : A){xs : List A} →
                        x ∈ xs → satisfies p x → x ∈ filter p xs
  lem-filter-complete p x {[]} () px

  lem-filter-complete p x {.x ∷ xs0} hd ⊤ with (p x)
  lem-filter-complete p x {.x ∷ xs0} hd () | false
  lem-filter-complete p x {.x ∷ xs0} hd ⊤  | true = hd

  lem-filter-complete p x {y ∷ xs0} (tl i') px with insp (p y)
  lem-filter-complete p x {y ∷ xs0} (tl i') px | it py prf with p y | prf
  lem-filter-complete p x {y ∷ xs0} (tl i') px | it .true prf  | true  | refl =
    tl (lem-filter-complete p x {xs0} i' px)
  lem-filter-complete p x {y ∷ xs0} (tl i') px | it .false prf | false | refl =
    lem-filter-complete p x {xs0} i' px

-- 3.4 an XML universe
module XML where
  open import Data.String

  Tag = String

  mutual
    data Schema : Set where
      tag : Tag → List Child → Schema

    data Child : Set where
      text : Child
      elem : ℕ → ℕ → Schema → Child

  data BList (A : Set) : ℕ → Set where
    []  : forall {n} → BList A n
    _∷_ : forall {n} → A → BList A n → BList A (suc n)

  data Cons (A B : Set) : Set where
    _∷_ : A → B → Cons A B

  FList : Set → ℕ → ℕ → Set
  FList A zero    m       = BList A m
  FList A (suc n) zero    = False
  FList A (suc n) (suc m) = Cons A (FList A n m)

  mutual
    data XML : Schema → Set where
      element : forall {kids}(t : Tag) → All Element kids → XML (tag t kids)

    Element : Child → Set
    Element text = String
    Element (elem n m s) = FList (XML s) n m

  -- (a)
  ap = Data.String._++_ -- FIXME: a clumsy way to avoid name clash...
  mutual
    printXML : {s : Schema} → XML s → String
    printXML (element t y) = 
      ap "<" (ap t (ap ">" (ap (printChildren y) (ap "</" (ap t ">")))))

    printBList : {s : Schema}{n : ℕ} → BList (XML s) n → String
    printBList [] = ""
    printBList (x ∷ xs) = ap (printXML x) (printBList xs)

    printChildren : {kids : List Child} → All Element kids → String
    printChildren {[]} all[] = ""
    printChildren {text ∷ xs} (p :all: y') = ap p (printChildren y')
    printChildren {elem zero m y0 ∷ xs} (p :all: y1) = ap (printBList p) (printChildren y1)
    printChildren {elem (suc n) zero y0 ∷ xs} (p :all: y1) = printChildren y1
    printChildren {elem (suc n) (suc m) y0 ∷ xs} ((x ∷ y) :all: y1) = 
        ap (printXML x) (printChildren {elem n m y0 ∷ xs} (y :all: y1)) 

-- 4.1 turn the type-checker for λ-calculus from section 3.1 into
-- a complete program that can read a file containing a raw λ-term
-- and print its type if it's well-typed and an error message otherwise
module Parse where
  open STLC.AbSyn

  open import Relation.Nullary

  open import Data.Product
  open import Data.String

  -- TODO: annotate with positions? this needs parsing
  -- TODO: also, might as well create a module [Syntax]
  -- devoted only to preterms
  data PreTerm : Set where
    var : String → PreTerm
    _app_ : PreTerm → PreTerm → PreTerm
    lam : String → Type → PreTerm → PreTerm
  NCx = List String

  data _⊢_⇔_ (Γ : NCx) : PreTerm → Raw → Set where
    -- "d" for "dangling"
    -- TODO: pass a proof attesting to the fact that this variable
    -- is not in the naming context, cf.
    --  not-found : forall {xs} → All (λ y → ¬(x ≡ y)) xs → FindEq x xs
    -- TODO: or actually, might introduce first pass on preterms
    -- devoted to stripping out names; it will either return a raw term
    -- without dangling variables or report any discrepancies. This
    -- is what real compilers do (e.g., ATS/Anairiats).
    dvar : {s : String}{m n : ℕ} → length Γ + m ≡ n → Γ ⊢ (var s) ⇔ (var n)
    var : {s : String}(p : s ∈ Γ) → Γ ⊢ (var s) ⇔ var (index p)
    _app_ : {p1 p2 : PreTerm}{e1 e2 : Raw} → Γ ⊢ p1 ⇔ e1 → Γ ⊢ p2 ⇔ e2 → Γ ⊢ (p1 app p2) ⇔ (e1 app e2)
    lam : forall {s τ p e} → (s ∷ Γ) ⊢ p ⇔ e → Γ ⊢ (lam s τ p) ⇔ (lam τ e)

  ap : {A : Set} → List A → List A → List A
  ap = Data.List._++_
  lem-find : {A : Set}{ys : List A}{y : A}(xs : List A) → y ∈ (ap xs (y ∷ ys))
  lem-find [] = hd
  lem-find (x ∷ xs) = tl (lem-find xs)

  data FindEq {A : Set}(x : A) : List A → Set where
    found : (xs : List A)(y : A) → x ≡ y → (ys : List A) → FindEq x (Data.List._++_ xs (y ∷ ys))
    not-found : forall {xs} → All (λ y → ¬(x ≡ y)) xs → FindEq x xs
  -- NOTE: tried to use [find] in conjunction with Data.String._≟_,
  -- but stumbled on (non-provability of?) (x == y) ≡ true → x ≡ y;
  -- hence, a supplementary function tailored to our need
  findStrEq : (x : String)(xs : List String) → FindEq x xs
  findStrEq x [] = not-found all[]
  findStrEq x (y ∷ xs) with Data.String._≟_ x y
  findStrEq x (.x ∷ xs) | yes refl = found [] x refl xs
  findStrEq x (y ∷ xs)  | no pf with findStrEq x xs
  findStrEq x (y ∷ ._)  | no pf | found xs z pz ys = found (y ∷ xs) z pz ys
  findStrEq x (y ∷ xs)  | no pf | not-found npxs = not-found (pf :all: npxs)

  removenames : (Γ : NCx)(p : PreTerm) → Σ[ x ∶ Raw ] Γ ⊢ p ⇔ x

  removenames Γ (var s) with findStrEq s Γ
  removenames .(ap xs (y ∷ ys)) (var .y) | found xs y refl ys =
    let pf = lem-find xs in var (index pf) , var pf
  removenames Γ (var s)                  | not-found pxs with insp (length Γ + suc zero)
  removenames Γ (var s)                  | not-found pxs | it n prf = var n , dvar prf

  removenames Γ (p1 app p2) with removenames Γ p1 | removenames Γ p2
  removenames Γ (p1 app p2) | e1 , pf1 | e2 , pf2 = e1 app e2 , pf1 app pf2

  removenames Γ (lam s τ p) with removenames (s ∷ Γ) p
  removenames Γ (lam s τ p) | e , pf = lam τ e , lam pf

module TypeChecker where
  open import IO
  open STLC.AbSyn
  open STLC.Check
  open Parse
  open import Data.Product
  open import Data.String

  -- TODO:
  -- * concrete syntax for STLC + recursive descent parser:
  --   parse : String → either String Raw

  fx : String → String → String
  fx = Data.String._++_

  report : {p : PreTerm}{e : Raw}{Δ : NCx}{Γ : Cxt} → Infer Γ e → Δ ⊢ p ⇔ e → IO ⊤
  -- Term Γ t
  report (ok τ t) pf = {!!} -- term [t] has type [τ]
  report (bad (var x)) (dvar{s} n) = putStrLn (fx "variable " (fx s " is out of scope"))
  report (bad (var x)) (var{s} n) = putStrLn (fx "variable " (fx s " is out of scope"))
  report (bad (y app0 y')) (y0 app y1) = {!!} -- in function application y @ y', y has no type
  report (bad (y app1 y')) (y0 app y1) = {!!} -- in function application y @ y', y has non-functional type
  report (bad (y app2 y')) (y0 app y1) = {!!} -- in function application y @ y', y' is expected to have type _ but has no type
  report (bad (app3 p y' y0)) (y1 app y2) = {!!} -- in function application y' @ y0, the type of y0 is expected to be ... but
                                                                                     -- is ...
  report (bad (lam τ)) (lam s) = {!!} -- in function abstraction lam s . b, b has no type
{-
      _app0_ : BadTerm Γ → Raw → BadTerm Γ
      _app1_ : Term Γ l → Raw → BadTerm Γ
      _app2_ : {σ τ : Type} → Term Γ (σ ⟶ τ) → BadTerm Γ → BadTerm Γ
      app3 : {σ σ' τ : Type} → (σ ≠ σ') → Term Γ (σ ⟶ τ) → Term Γ σ' → BadTerm Γ
      lam : {σ : Type} → BadTerm (σ ∷ Γ) → BadTerm Γ
-}
  typecheck : PreTerm → IO ⊤
  typecheck p with removenames [] p
  typecheck p | (e , pf) = report (infer [] e) pf


{-
  typecheck x with infer [] x
  typecheck .(erase t) | ok σ t = {!!} -- "term [t] has type [σ]"

  -- "typechecking failed due to ..."
  typecheck .(eraseBad e) | bad e = {!!}
-}
{-
  typecheck .(var n) | bad (var {m} {n} y) = {!!} -- FIXME: how to print name here?
                                                  -- ah, keep a list of names somewhere?
                                                  -- it will have to be the same length as the context, always;
                                                  -- well, we could also introduce "pre-terms" which are named
  typecheck .(eraseBad y app y') | bad (y app0 y') = {!!}
  typecheck .(erase y app y') | bad (y app1 y') = {!!}
  typecheck .(erase y app eraseBad y') | bad (y app2 y') = {!!}
  typecheck .(erase y' app erase y0) | bad (app3 y y' y0) = {!!}
  typecheck .(lam σ (eraseBad y)) | bad (lam {σ} y) = {!!}
-}
  main : IO ⊤
  main = putStrLn "Hello world!"
