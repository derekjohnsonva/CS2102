/- *** I. FORMAL LANGUAGES *** -/

/-
Propositional logic is a formal language
with a syntax and a semantics. Its syntax
is simple: literal true and literal false
are expressions; variables such as P and
Q are are expressions; and if e1 and e2 
are expressions, then so are ¬ e1, e1 ∧ e2, 
e1 ∨ e2, e1 → e2, and so on.

The semantics of propositional logic are
equally simple. Literal true and false
expressions evaluate to Boolean true and
false values, respectively. Variable
expressions are evalauted with respect
to an interpretation function that, to
each variable, assigns a Boolean value.
Operator expressions are evaluated
recursively. For example, to evaluate
¬ e1, we evaluate e1 (recursively, with
respect to a given interpretation) to
obtain a Boolean value, then we return
the Boolean negation of that value. To
evaluate e1 ∧ e2, we evaluate e1 and
e2 with a given interpretation and then
return the Boolean conjunction (and) of
the resulting Boolean values.

Other formal languages essential for
work in computer science and discrete
mathematics, including predicate logic,
also have a formal syntax and semantics. 
Another simple example is the language
of arithmetic expressions involving the
natural numbers.

Expressions in this language include
literal *numeric* values, variable
expressions, and operator expressions.
Consider, for example, the following
arithmetic expressions, written in
everyday mathematical notation:

1       -- literal 1
X       -- variable expression
1 + X   -- binary operator expression
x!      -- unary operator expression

Your task on this question is to
formalize (by implementing in Lean)
a very simple arithmetic expression
language. Your solution can be based
(modeled) on our formalization of the 
syntax and semantics of propositional
logic.
-/


/-
A. Variables

To support the formation of 
*variable expressions*, and the 
definition of *interpretations*
that we can use to evaluate such
expressions, define a type, var,
the values of which we will take
to represent variables. 

This type should have just one 
constructor. Call it mk. To provide
for an infinite supply of "variables",
define the constructor to take one
argument of type ℕ.

Hint: model your solution on the var 
type we defined to specify the syntax
of propositional logic. 
-/ 

inductive var : Type
| mk : ℕ → var

/-
Now define xVar, yVar, zVar, and
wVar, to be identifiers bound to 
values of type var, with "indices" 
(i values) of 0, 1, 2, and 3, 
respectively.
-/
open var
def xVar := mk 0
def yVar := mk 1
def zVar := mk 2
def wVar := mk 3

/-
B. Interpretations

To support the interpretation
of variable expressions (each of
which will "contain" an object of
type var), we will apply functions 
of type (var → ℕ) to var values 
to "look up" their values "under 
the given interpretation". 

Here you are to define two such
interpretation functions. The first
will return the natural number, 0
(of type ℕ) for any var. The second
return 3 for xVar (var.mk 0), 5 for
yVar, 7 for zVar, 9 for wVar, and 
zero for any other "variable" (var). 

You may use whatever style of
function definition you prefer.
Call your interpretation functions 
zeroInterp and otherInterp, resp. 
-/


-- 1. Define zeroInterp here

def zeroInterp : var → ℕ 
| _ := 0

-- 2. Define otherInterp here
def otherInterp : var → ℕ
| (var.mk 0) := 3
| (var.mk 1) := 5
| (var.mk 2) := 7
| (var.mk 3) := 9
| _ := 0

-- Hint: it's easiest to define by cases
-- Hint: put patterns in parentheses

-- etc


/- C. Expressions

Your next task is to specify the
syntax of our arithmetic language. 
Do this much as we did for our
syntax for propositional logic: by
defining a type called aExpr, the
values of which are expressions in
our new expression language. Call
the type aExpr.

It should provide four constructors:
litExp, varExp, facExp, plusExp. 
The litExp constructor takes a natural 
number, n, as an argument and builds
a literal expression for that value.
The varExp constructor should take a
variable (of type var) as a value
and constructs a variable expression
for that var object. FacExp takes one
expression as an argument and yields
an expression that we will understand
to mean e!, that is, "e factorial".
Finally, plusExpr should take two 
expressions, e1 and e2, and yield 
an expression meaning e1 + e2.
-/ 

inductive facOp : Type
| factorial

inductive plusOp : Type
| plus


inductive aExpr : Type
| litExp : ℕ → aExpr
| varExp : var → aExpr
| facExp :  aExpr → aExpr
| plusExp : aExpr → aExpr → aExpr
-- give the rest


open aExpr

/-
Concrete notation. You may use the
following notation.
-/

notation e1 + e2 := plusExp e1 e2

/-
Now define the following expressions
-/

-- literal expression for 2
def L2 : aExpr := litExp 2

-- literal expression for 4 
def L4 : aExpr := litExp 4

-- variable expressions X for xVar,
-- Y for yVar, Z for zVar, W for wVar
def X : aExpr := varExp xVar
def Y : aExpr := varExp yVar
def Z : aExpr := varExp zVar
def W : aExpr := varExp wVar

-- operator plus expressions for the
-- following, using our notations 

-- 2 + 4
def L2plusL4 := plusExp L2 L4

-- X + Y + Z + W + 2
def bigSum := plusExp ( plusExp((plusExp X Y) (plusExp Z W))) L2

-- Z!

def zFactorial : aExpr := facExp Z


/- E. Operational Semantics

Now define an "operational semantics" 
for our language by defining a function,
aEval, that takes any expression, e, and 
an interpretation, i, and reduces e to a
natural number as follows: (i) a literal
expression reduces to the natural number
it "contains"; (2) a variable expression
reduces to the value of the var object it
"contains", "under the interpretation, i";
(3) a plus expression reduces to the 
natural number sum of the reduced values
of its two subexpressions (under i); and 
(4) a (facExpr e) reduces to the factorial 
of the value of e under i. 

Before writing the aEval function, itself,
write a fac function that takes any natural 
number, n, and that returns the factorial 
of n. You'll need this function to finish
your aEval function. 
-/

-- Your answer here
open nat
def fac : ℕ → ℕ 
| zero := (succ zero)
| (succ n') := (succ n') * (fac n')

-- Write your aEval function here
def aEval : aExpr → (var → ℕ) → ℕ
| (litExp n) _ := n
| (varExp v) i := i v
| (facExp e) i := var.mk (fac e)
    
| (binOpExp op e1 e2) i := 
     ( op)
        (pEval e1 i) 
        (pEval e2 i)
-- the rest goes here

/-
Here are some test cases you can use to
check if your aEval function and everything
else is working properly.
-/ 

#reduce aEval L2plusL4 zeroInterp
#reduce aEval bigSum zeroInterp
#reduce aEval zFactorial zeroInterp

#reduce aEval L2plusL4 otherInterp
#reduce aEval bigSum otherInterp
#reduce aEval zFactorial otherInterp


/- *** II. PREDICATE LOGIC *** -/

/- A. Formalizing natural language 

For each of the following propositions
expressed in natural language, make it
formal by expressing it as a proposition
in predicate logic.
-/

/- 1. 
There exist three natural numbers, a,
b, and c, such that a^2 + b^2 = c^2.
-/

def py : Prop :

/-
For the following problem, we assume
that Person is a type whose values
represent individual people; that 
Nice is a property of people; and 
that Likes is a binary relation on
people. 
-/

-- Mary, Lu, and Robert are people
inductive Person : Type 
| Mary
| Lu
| Robert

open Person

/- 2.

Formalize the concept that (1) Nice
is a property of people and that Mary
and Lu are nice. Hints: formalize this
property as a predicate (proposition
with one argument) on Persons, with
proofs that "Mary is Nice" and "Lu is 
Nice." Give (constructor) names to
these proofs: nice_mary and nice_lu. 
-/


inductive is_nice : Person → Prop
| nice_mary : is_nice Mary
| nice_lu : is_nice Lu

-- Answer

/- 3.

Formalize the concept that (1) Likes
is a binary relation on people and (2)
Mary like Robert and Robert likes Lu. 
Hint: give names to proof constructors.
-/

-- Answer


/- 4.

a. Formalize the proposition that everyone
(every Person) likes someone (some Person). 
-/

def everyone_likes_someone : Prop :=
    _

/-

b. Formally state (don't try to prove) the 
proposition that Likes is a transitive 
relation (even though it's not, as defined).
-/

def likes_is_trans : Prop := 
    _


/- B. Naturalizing formal language.

Translate each of the following formal
propositions into *natural* natural languages.
Don't just translate the logical symbols into
words, but say what the proposition means in
terms that would be understandable to most
anyone. 
-/

def p1 := ∃ (p : Person), ∀ (q : Person), ¬ Likes p q

-- Answer (try to say it in three words): someone likes everyone

def p2 := ¬ ∃ (p : Person), ∀ (q : Person), Likes p q

-- Answer (try to say it in no more than four words): noone likes everyone

def p3 := ∀ (n : ℕ), fac n = 1 → n = 0 ∨ n = 1

-- Here fac means the factorial function.
-- Answer (hint: use if ... then ... ) if the factorial of n is one
-- then n is equal to zero or one


/- *** III. PROOFS *** -/


/- A. Proofs in natural language -/

/-
Let us define "beautiful" as a property of
natural numbers, as follows. First, the 
natural number, 1, is beautiful. Second, 
if any natural number, n, is beautiful, 
then so is 3 * n + 1. Finally, if a natural
number, n, is beautiful, then so is n * 2.
-/

/- 1. 

Give a natural language proof that 8 is
beautiful. Hint: Think backwards from 8.
Start as follows: "To show that 8 is 
beautiful, our axioms (rules) imply that
it will suffice to show that ____ is a
beautiful number." Then carry on from 
there.
-/

/-
Answer: 
To show that 8 is 
beautiful, our axioms (rules) imply that
it will suffice to show that 4 is a
beautiful number.
To show that 4 is 
beautiful, our axioms (rules) imply that
it will suffice to show that 2 is a
beautiful number
To show that 2 is 
beautiful, our axioms (rules) imply that
it will suffice to show that 1 is a
beautiful number

We know that 1 is a beautiful number because it is 
the first axiom given. One is a beautiful number 
therefore, 8 is a natural number
-/

/- 2.

Prove that 13 is beautiful. 

To show that 13 is 
beautiful, our axioms (rules) imply that
it will suffice to show that 4 is a
beautiful number

To show that 4 is 
beautiful, our axioms (rules) imply that
it will suffice to show that 1 is a
beautiful number

We know that 1 is a beautiful number because it is 
the first axiom given.
-/

/- 3.

Give a natural language proof of 
the following proposition:
(1 = 0 + 1) ∧ (3^2 + 4^2 = 5^2). 

Be sure to make clear what inference
(introduction and/or elimination) 
rules of natural deduction, and what 
other axioms (e.g., of equality), you
are using to prove it.

Using the reflexive property of equality and knowing
that any natural number plus zero will equal itself we can prove
1 = 0 + 1

Using the reflexive property of equality and the 3,4,5 right angle
property of triangles we can prove the second assertion

Since both are true, the proposition is true
-/


/- 4.

Consider the following formal definition
of binary relation on people. A pair of
"Persons", (p1, p2), is in this relation 
if and only if p1 is "older than" p2. 

Give a natural language proof that this
relation is transitive. As part of your
answer, state precisely what it means 
for a relation to be transitive, and then 
explain exactly why this relation meets this 
definition.
-/

inductive Older : Person → Person → Prop
| m_older_r : Older Mary Robert
| r_older_l : Older Robert Lu
| m_older_l : Older Mary Lu

/-
Natural Language Proof:
    if a relationship is transitive it means that 
    two existences of the relationship can be combined 
    to show a proof of the new relationship.
    if a > b and b>c, a>c

-/

/- B. Formal Proofs -/

/-
Given formal proofs of the following
propositions in predicate logic. 
-/


/-
Note: The keyword, "example", in the following
problems is just like theorem but just omits
giving give a name to a proof.
-/

example : ∀ (P Q : Prop), P → Q → (Q ∧ P) :=
    begin
        intros,
        exact and.intro a_1 a
    end


example : ∀ (P Q : Prop), P ∧ Q → P :=
    begin
    intros,
    exact and.elim_left a,
end


example : ∀ (P Q R : Prop), (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
    begin
        intros P Q R pandq qandr,
        have p := and.elim_left pandq,
        have r := and.elim_right qandr,
        exact and.intro p r,
    end


example : ∀ (P Q : Prop), ((P → Q) ∧ P) → Q :=
    begin
        intros P Q x,
        have pimpq := and.elim_left x,
        apply pimpq,
        apply and.elim_right x,
    end 


example : ∀ (P Q : Prop), (P ∧ Q) → (Q ∧ P) :=
    begin
        intros P Q pandq,
        apply and.intro (and.elim_right pandq)(and.elim_left pandq)
    end


-- Extra credit questions

example : ∀ (a b c : ℕ), a = b → b = c → a = c :=
    begin
        intros a b c aeqb beqc,
        apply eq.subst,
        apply beqc,
        apply aeqb,
    end


example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
    begin
        intros P Q pimpq nq, 
    end