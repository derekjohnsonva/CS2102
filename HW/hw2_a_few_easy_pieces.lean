/-
UVa CS Discrete Math (Sullivan) Homework #2
-/

/-
Note: We distribute homework assignments and
even exams as Lean files, as we do now for this
assignment. You will answer the questions in one 
of two ways: by writing an answer in a comment block 
(such as this one), or by writing mathematical logic 
(which is what "Lean code" is). For this assignment
you will write all your answers as simple comments.
-/

/-
This assignment has three questions, each with several 
parts. Be sure to read and answer all parts of all of
the questions.

Make a copy of this file in your "mywork" directory
the read and answer the questions by editing this fie.
When you are done, *save it*, then upload it to Collab. 
That is how you will submit work in this class. Be sure 
to double check your submission to be sure you uploaded the right file.
-/

/-
QUESTION #1 (7 Parts, A - G)

A. How many functions are there that take one
argument of type Boolean (one bit, if you prefer)
and that return one value, also of type Boolean?
Hint: We discussed this in class.

Answer here (inside this comment block): 4

B. How many functions are there that take two
arguments of type Boolean and that return
one value of type Boolean? Hint: we discussed
this in class, too. 

Answer here: 16

C. How many functions are there that take three
bits of input and that return a one bit result?
Hint: We discussed this, too.

Answer here: 256

D. Give a general formula that you believe to
be valid describing the number of functions
that take n bits, for any natural number, n,
and that return one bit. Use the ^ character
to represent exponentiation.

Answer:(2^(n))^2

E. How many functions are there that take three
bits of input and that return *two* bits as a
result? Hint: think about both how many possible 
combinations of input bits there are. To define
a function, you need to specify which two-bit
return value is associated with each combination
of input values. The number of functions will be
the number of ways in which you can assign output
values for each combination of input values. Give
your answer in a form that involves 3 (inputs)
and 2 (output bits).

Answer here: 4096


F. How many functions are there that take 64 bits
of input and return a 64 bit result? Give your 
answer as an algebraic expression. The number is
too big to write it out explicitly.

Answer here: (2^(64))^(2^(64))

G. How many functions are there that take n bits of
input and return m bits of output, where n and m are
natural numbers? Give an algebraic expression as your
answer, involving the variables m and n.

Answer here: (2^n)^(2^m)
-/

/- 
QUESTION #2 (Three parts, A - C)

Suppose you are asked to write a program, P(x), taking 
one argument, x, a "natural number", and that it must 
satisfy a specification, S(x), that defines a function 
in a pure functional programming language. 

A. Using simple English to express your answer, what 
proposition that must be true for P to be accepted as a 
correct implementation of S. Hint: We discussed this in 
class.

Answer: P must satisfy specification s for every possible value of x.

B. Why is testing alone generally inadequate to prove 
pthe correctness of such a program, P?

Answer: There are often too many testing variations to prove by testing alone

C. What kind of mathematical "thing" would be needed to 
show beyond a reasonable doubt that P satisfies S? You 
can give a one-word answer.

Answer: proof

-/



/- 
QUESTION #3 (Four parts, A - D)

Consider a new data type, cool, that has three possible
values: true (T), false (F), and don't know (D). And now
consider the following conjecture:

For any natural number, n, the number of combinations 
of values of n variables of type cool is 3^n.

Give a proof of this conjecture by induction.

A. What is the first conjecture you must prove? Hint:
substitute a specific value for n into the conjecture
and rewrite it with that value in place of n.

Answer: You have to prove the base case. In our situation that would be n=0. 
When n = 0, the number of combinations should be 1. If we plug 0 into the equation 3^n we get
the value 1 out. The base case is established.

B. Prove it. Hint: One approach to proving that two
terms are equal is simply to reduce each term to its
simplest form, and then show that the reduced terms
are exactly the same. In other words, just simplify
the expressions on each side of an equals to to show
that the values are identical.

Answer here: We know that in mathematics the number of variations of zero variables is 1. 
If we have n = 0, the number of variables should be 1. When we plug n = 0 into 3^n it evaluates
to 1. We can see that our base case meets our expected output.

C. What is the second conjecture that you must prove
to complete your proof by induction?

Answer here: If the states of n variables is 3^n then the states of (n+1) is equal to 3^(n+1). In 
simpler terms, adding another variable should increase the number of possible combinations 
by 3 times. 


D. Prove it. Hint, to prove a proposition of the form,
P → Q, or P implies Q, you start by *assuming* that P
is true (whatever proposition it happens to be), and 
then you show that in the context of this assumption,
that proposition Q must be true. In other words, you
want to prove that IF P is true THEN Q must be true,
too.

Answer here: If we assume that 3^n equals the number of combinations, then 
it must be true for 3^(n+1). 3^(n+1) is equal to (3^n)*3. We can use use another example in 
which we know the expected output to demonstrate this. The combinations with 1 variable should 
be 3. 3^(1) = 3^(0)*3, 3^(0)=1, therefore, 3^1 = 3. 

-/


