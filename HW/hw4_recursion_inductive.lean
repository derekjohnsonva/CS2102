/-
Problem #1. We give you a simple "natural 
number arithmetic abstract data type based
on our own mnat type for representing the 
natural numbers. You are to extend it by 
adding definitions of several operations
(functions). 

The first is a boolean "less than" 
operator. It will take two natural 
numbers and return true (tt) if and only 
if the first is less than the second 
(otherwise it will return false). 

The second function will implement mnat
multiplication. It will use recursion and
the given definition of mnat addition.

The third function will implement the
factorial function using the mnat type.
The factorial of zero is one and the 
factorial of any number n = 1 + n' is
n times the factorial of n'. 
-/

-- Here's the logic we've already covered.

namespace mynat

inductive mnat : Type
| zero
| succ : mnat → mnat

open mnat 

-- an increment function
-- takes mnat, returns one greater nmat
def inc : mnat → mnat :=
    λ n : mnat, succ n

-- alternative syntax (c-style)
def inc' (n : mnat) : mnat :=
    succ n

-- is_zero predicate
-- return tt iff and only if mnat is zero 
def is_zero : mnat → bool
| zero := tt
| _ := ff

-- predecessor
-- returns zero when mnat is zero
-- else returns one less than given mnat
def pred : mnat → mnat 
| zero := zero
| (succ m) := m

-- equality predicate
-- tt if given mnats are equal else ff
def eq_mnat : mnat → mnat → bool
| zero zero := tt 
| zero (succ m) := ff
| (succ m) zero := ff
| (succ m) (succ n) := eq_mnat m n

-- mnat addition
-- by cases on first argument
-- zero + any m returns m
-- (1 + n') + m returns 1 + (m' + n)
-- understand why the recursion terminates
def add_mnat : mnat → mnat → mnat
| zero m := m
| (succ n') m := succ (add_mnat n' m)


/- [20 points]
#1A. Implement an mnat "less than" 
predicate by completing the following 
definition. Fill in the placeholders.
-/

def lt_mnat : mnat → mnat → bool
| zero zero := false
| zero _ := true
| (succ n') zero := false
| (succ n') (succ m') := lt_mnat n' m'

-- When you succeed, the following tests
-- should all give the right answers.
def mzero := zero
def mone := succ zero
def mtwo := succ (succ zero)
def mthree := succ (succ (succ zero))
def mfour := succ (succ (succ (succ zero)))


#reduce lt_mnat mzero mzero
#reduce lt_mnat mzero mtwo
#reduce lt_mnat mtwo mtwo
#reduce lt_mnat mtwo zero
#reduce lt_mnat mtwo mthree
#reduce lt_mnat mthree mtwo 

/- [20 points]
#1B. Implement an mnat multiplication
function by completing the following
definition. Hint: use the distributive
law. What is (1 + n') * m? Also be sure
you see why the recursion terminates in 
all cases.
-/

def mult_mnat : mnat → mnat → mnat
| zero _ := zero
| (succ n') m := add_mnat m (mult_mnat n' m)

-- When you succeed you should get
-- the right answers for these tests
#reduce mult_mnat mzero mzero
#reduce mult_mnat mzero mthree
#reduce mult_mnat mthree mzero
#reduce mult_mnat mtwo mthree
#reduce mult_mnat mthree mtwo
#reduce mult_mnat mthree mthree


/- [10 points]
#1C. Implement the factorial function
using the mnat type. Call your function
fac_mnat. Give a definition by cases using
recursion, in the style of the preceding
examples.
-/

def fac_mnat : mnat → mnat
| zero := inc zero
| (succ n) := mult_mnat (succ n) (fac_mnat n) 


-- Add test cases for zero, one, and
-- some larger argument values and check
-- that you're getting the right answers.
#reduce fac_mnat mzero
#reduce fac_mnat mone
#reduce fac_mnat mtwo
#reduce fac_mnat mthree
-- Here

end mynat



/-
#2. Inductive data type definitions.

For this problem, you will extend a 
very simple "list of natural numbers"
abstract data type. The technical term
for a list is a "sequence". You will 
first read understand a list_nat data 
type and you will then define several
functions that operate on values of
this type. As you work through these
problems, note their similarity to
comparable functions involving the
natural numbers (such as is_zero,
succ, pred, and add).
-/

namespace my_list_mnat

open mynat 

/-
The following inductive definition
defines a set of terms. The base case is
nil, representing an empty list of mnat.
The cons constructor on the other hand
takes an mnat (let's call it h) and any
list of mnats (call it t) and returns the
term, (cons h t), which we interpret as a
one-longer list with h at its "head" and
the one-smaller list, l, as its "tail"). 
-/
inductive list_mnat : Type
| nil
| cons : mnat → list_mnat → list_mnat

open list_mnat 

-- Here are two list definitions using
-- our new data type

-- representation of an empty list
def empty_list := nil

-- representation of the list [1, 2, 3]
def one_two_three := 
    cons 
        mone 
        (cons 
            mtwo 
            (cons 
                mthree
                nil
            )
        )
#eval mone
#eval mtwo
#eval one_two_three
/-
2A. [10 points]

Define three_four to represent the
list [3, 4].
-/

-- Here
def three_four :=
    cons
        mthree
        (cons
            mfour
            nil
        )

#eval three_four

/-
#2B. [10 points]

Implement a predicate function,
is_empty, that takes a list_mnat and
returns true if an only if it's empty,
otherwise false.
-/

-- Your answer here

def is_empty : list_mnat → bool
| nil := true
| _ := false

#eval is_empty empty_list  --true
#eval is_empty three_four --false
/-
#2C. [10 points]

Implement a prepend_mnat function
that takes an mnat, h, and a list_mnat,
t, and that returns a new list with h
as the value at the head of the list
and t as the "rest" of the new list (its
"tail").
-/

-- Your answer here
def prepend_mnat : mnat → list_mnat → list_mnat
| h t := cons h t

#eval prepend_mnat mtwo empty_list
#eval prepend_mnat mzero empty_list


/-
#2D. [10 points]

Implement a "tail_mnat" function 
that takes a list_mnat, l, and returns 
the following. If l is nil, then nil; 
otherwise (in which case l = (cons h t)for some h and some t) then t.
-/

-- Your answer here
def tail_mnat : list_mnat → list_mnat
| nil := nil
| (cons h t) := t

#eval three_four
#eval tail_mnat three_four
#eval tail_mnat one_two_three
/-
#2E. [10 points]

Implement a "length_mnat" function
that takes any list_mnat and returns its
length. The length of the empty list is
zero and the length of any non-empty list,
(cons h t) is of course one more than the
length of t.
-/
def length_mnat : list_mnat → ℕ 
| nil := 0
| (cons h t) := 1 + (length_mnat t)

#eval length_mnat empty_list
#eval length_mnat three_four
/-
2F. [Extra Credit]

Implement an append_mnat function. 
It takes two list_mnat values and returns
a new one, which is the first appended
to (and followed by) the second. So, for
example, the list [1, 2] appended to the
list [3, 4, 5] should return the list,
[1, 2, 3, 4, 5]. Of course you won't be
using this nice list notation, just the
constructors we've defined.

To understand how to solve this problem,
start by really thoroughly seeing how the
addition function for mnats works. It 
uses recursion on the *first* of the two
arguments. If the first argument is zero,
it returns the second argument without 
change. Similarly, here, if the first list
is nil, the result is the second list. If
the first list is not nil, then it must
be of the form (cons h t). In this case,
the head of the new list will be h. What
will be the tail of the new list?
-/

-- Your answer here| 

--append_mnat t (cons h o)
def append_mnat : list_mnat → list_mnat → list_mnat
| nil h := h
| (cons h t) o := cons h (append_mnat t o)
                    


#eval one_two_three 
#eval append_mnat empty_list one_two_three
#eval append_mnat one_two_three one_two_three
/-
Add tests where the first list is nil and
not nil, and make sure you're getting the
right answers.
-/ 


end my_list_mnat

/-
This is the end of the homework. Please 
be sure to save your file before uploading
then check that you uploaded correctly. We
cannot accept work submitted incorrectly
or late, so take a minute to be sure you
got it right. Thank you!
-/