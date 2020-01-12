/-
Styles of function writing
    1) "C" style
    2) tactic script
    3) lambda abstraction
-/
def square : ℕ → ℕ 
    | n := n*n


def square' : ℕ → ℕ :=
    λ n, n^2

#eval (λ (n : ℕ ), n^2) 3

def x := λ (n:ℕ ), n^2

#check x

/-
Must really know how to write lambda expressions
-/
def x' := λ (n : bool), tt

/-
Be able to produce recursive function definitions (in Lean) for simple
arithmetic functions. Know how to reason about and write appropriate base 
and recursive cases for functions involving natural numbers. A base case 
generally involves an argument value of nat.zero. A recursive case generally 
occurs when an argument value is of the form (nat.succ n') for some n'. These
two cases correspond to the two constructors for the nat data type. You might 
be tempted to name the argument in a recursive case n, and to recurse on the 
expression "n minus 1" but this will not work in Lean, because Lean cannot then 
prove to itself that the recursion terminates. The definition of the factorial 
function (in Lean) is a good example to study. 
-/

--recursive find fibonaci
open nat
def fib : ℕ → ℕ 
    |nat.zero := nat.zero
    | (succ(nat.zero)):= (succ(nat.zero))
    | (succ(succ n')) := fib(n') + fib(n' + 1)

def fact : ℕ → ℕ 
    | nat.zero := succ nat.zero
    | (succ(nat.zero)):= (succ(nat.zero))
    | (succ n') := fact (n') * (succ n')

#eval fact 4

/-
Understand key tradeoffs when defining functions using mathematical logic, and
using imperative programming languages, respectively
Answer: mathematical logic can be easier to understand and explain but imperative
programming allows for more efficient use of computational resources as
well as fewer lines of code
-/

/-
Understand key shortcomings of natural languages for expressing mathematical 
(including specification and implementation) concepts.
Answer: Natural Language: The language that we all speak.
Not the language that machines operate using. There is too much 
ambiguity in natural language. It is not checkable by machines.

Formal Language: ex Python, boolean algebra. Well defined
language with no ambiguity. Some formal languages are based
off of the structure of natural language(ex. cobol)
-/

/-
Understand precisely what it means for a program to be correct with respect to 
(or "equivalent" to) a specification written in math logic.
-/

/-
Know Boolean function truth tables
-/

/-
Know how lists ("sequences") are inductively defined and be able to define
recursive functions that operate on lists

inductive nat : Type
| zero : nat
| succ : nat → nat
-/
open nat
inductive list_nat : Type
| nil
| cons : nat → list_nat → list_nat
open list_nat
--Recursive list function
def length_nat : list_nat → ℕ 
| nil := 0
| (cons h t) := 1 + (length_nat t)

def append_mnat : list_nat → list_nat → list_nat
| nil h := h
| (cons h t) o := cons h (append_mnat t o)

/-
Know how to define polymorphic functions that work with values of type 
(list alpha), where alpha is a type parameter. Understand implicit 
arguments and how to use them in Lean function definitions.

def unbox' (α : Type) : boxed α → α
| (box v) := v

def unbox {α : Type} : boxed α → α 
-- Use curly braces to indicate implicit arg
| (box v) := v
-/

/-
Know how to define simple enumerated types in Lean and functions
that operate on values of such types. The "day" type that we covered
is an example of such a type.
-/
inductive day : Type  
 | sun : day
 | mon : day
 | tue : day 
 | wed : day 
 | thu : day 
 | fri : day 
 | sat : day


inductive mybool : Type
    | ttt
    | fff

open day
def nextDay : day → day 
 | sun := mon
 | mon := tue
 | tue := wed 
 | wed := thu 
 | thu := fri 
 | fri := sat 
 | sat := sun

/-
Understand the higher-order "map" and "reduce" functions 
that we've studied. The key characteristic of higher-order 
functions is that they take function arguments, or return 
functions as results, or both. Be able to implement and use 
map and reduce functions. 
-/
open list
def map_pred : (ℕ → bool) → list nat → (list bool)
| _ [] := []
| f (cons h t) := 
    if (f h)
    then (cons tt (map_pred f t))
    else (cons ff (map_pred f t))

-- Answer here
def b_list := [0,1,2,5,1,0]

def reduce_and : list bool → bool 
| [] := tt 
| (cons ff t) := ff
| (cons tt t) := reduce_and t

/-
Understand how to specify and work with "product" types. 
The "prod" type we defined is an example of a type whose 
values are ordered *pairs* of values of other specified types.

Ans: A polymorphic "product type", prod. A product
type is a type whose values are ordered pairs.
Here the types of the first and second elements
of such a pair are given by the values of two
type arguments, α and β respectively. The pair
constructor takes a value of type α and one of
type β and yeilds the term (pair a b), whic we 
will interpret as representing the ordered pair,
(a, b), a concept that should be familiar from
basic high school algebra.
-/

inductive prod2 (α β : Type) : Type
| pair (a : α) (b : β) : prod2

def fst {α β : Type} : prod2 α β → α 
| (prod2.pair a b) := a

def snd {α β : Type} : prod2 α β → β 
| (prod2.pair a b) := b


/-
Understand the combinatorics of binary values. E.g., 
there are 2^n possible values of a sequence of n 
binary variables.

(2^(n))^(2^m) = number of posible functions with n 
input bits and m output bits
-/