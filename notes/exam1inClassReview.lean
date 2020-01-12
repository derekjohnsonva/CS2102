/-
The identity function for any type
-/

namespace review
--polymorphic identity function
def id (α : Type) (a : α) : α := a 

#eval id bool tt
#eval id string "Hello"

--does the same thing as id but with different notation
def id' (α : Type) : α → α 
| a := a

#eval id' bool tt
#eval id' string "Hello"

--Type Inference
-- {} allows for implicit arguments
def id'' {a : Type} : a → a
| a := a
#eval id'' tt
#eval id'' "Hello"
#check (@id'' nat) --@ turns off implicit arguments


/-
Polymorphic Data Type
We will be making boxed again to practice
-/

inductive boxed_nat : Type
| box_nat : ℕ → boxed_nat 
--another way to do the same thing as above
inductive boxed_nat' : Type
| box_nat (n : ℕ) : boxed_nat'
open boxed_nat 
def unbox_nat : boxed_nat → ℕ 
| (box_nat v) := v

--This makes the Data Type Polymorphic
inductive boxed (α : Type) : Type
| box : α → boxed

open boxed
def unbox {α : Type} : boxed α → α
| (box v) := v


/-
We are going to be making a new Polymorphic Data Type
First lets talk about set theory:
    Set Product:
        When we take two sets and combine them, we get
        every possible combination of the elements of the 
        two sets

Our new data type will be called Prod
-/

inductive prod (α β: Type) : Type
| pair (a : α) (b : β) : prod

def fst {α β : Type} : prod α β → α
| (prod.pair a b) := a

def snd {α β : Type} : prod α β → β
| (prod.pair a b) := b

def p1 := prod.pair 3 "Hello"
#eval fst p1
#eval snd p1
end review