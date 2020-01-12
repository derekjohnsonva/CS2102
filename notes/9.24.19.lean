/-
Domain of Discourse = "World"
    the area of math that you are talking about. Ex, Boolean Algebra

Syntax Terms: Values that carry meaning

Syntax Terms are interpreted in the Domain of Discourse for which it belongs

The interpretation is known as semantics

-/

namespace mlist
open list  --Lean-provided data type
/-
Lists in Lean are "polymorphic". They can contain
elements of any specified type

inductive nat : type :=
| zero
| succ: nat -> nat  
-/

def e : list nat := nil
#check e
#eval e

def l1 : list nat :=
    cons
        1   -- head element
        nil --tail list

-- cons constructor is of type list to nat

def my_list : list string := 
    cons
        "I"
        (
        cons
            "Love"
                (
                cons
                    "discrete Math"  
                    nil     
                )
        )
#eval my_list

def my_list' : list string :=
    ["I", "love","DM"]

def l4 : list nat := [1,2,3,4]

/-
To build list of nat

Inductive list-nat : type := 
| nil
| cons : nat -> list-nat -> list-nat
-/

--Functions on lists
def prepend : nat →  list nat → list nat 
| h t := cons h t

#eval prepend 1[2,3,4]


def mhead : list nat → nat
| nil := 0
| (cons h t) := h

def mtail : list nat → list nat
| nil := nil
| (cons h t) := t 

def mlength : list nat → nat
| nil := 0
| (cons h t) := 1 + (mlength t)


/-
Warmup, create a function definition that given a 
natural number will return a list of natural numbers
counting down.
-/
def countdown : ℕ → list nat 
| 0 := cons 0 nil 
| (nat.succ n) := cons (nat.succ n) (countdown (n))


#eval countdown 10
--More Recursion
def fib : ℕ → ℕ   
|nat.zero := nat.zero
|(nat.succ (nat.zero)) := (nat.succ (nat.zero))
| (nat.succ (nat.succ n)) := fib(n) + fib (n+1)

#eval fib 10
#eval fib 3

def mdouble : list ℕ → list ℕ 
| [] := []
| (cons h t) := cons (h*2) (mdouble t)

def mmap : (ℕ → ℕ ) → list ℕ → list ℕ  
| f [] := []
| f (cons h t) := cons (f h) (mmap f t)

#eval mmap nat.succ [1,2,3,4]
#eval mmap (λ (n:ℕ), n*n) [1,2,3,4]

def mreduce_add : list ℕ → ℕ 
| [] := 0
| (cons h t) := h + (mreduce_add t)

#eval mreduce_add [1,2,3,4,5,6]

--map recude function
def mreduce : (nat → nat → nat) → nat → (list nat) → nat
| f id [] := id 
| f id (cons h t) := f h (mreduce f id t)

#eval mreduce nat.add 0 [1,2,3,4,5]
#eval mreduce nat.mul 1 [1,2,3,4,5]

end mlist