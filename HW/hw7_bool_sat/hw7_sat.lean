/-
Derek Johnson dej3tc
11/1/2019
-/

import .prop_logic 
import .bool_sat

open prop_logic 
open prop_logic.var
open prop_logic.pExp


/-
An example: The 0th, 1st, and 
2nd bits from the right in 100, 
the binary numeral for decimal
4, are 0, 0, and 1, respectively.
-/
#eval mth_bit_from_right_in_n 2 4

/-
#1. Write and evaluate expressions
(using eval) to determine what is 
the bit in the 9th position from
the right in the binary expansion
of the decimal number 8485672345? 

Hint: don't use reduce here. Eval
uses hardware (machine) int values
to represent nats, while reduce 
uses the unary nat representation. 

Self-test: How much memory might 
it take to represent the decimal
number, 8485672345, as a ℕ value
in unary?
-/

#eval mth_bit_from_right_in_n 9 8485672345


/-
The next section presents examples
to set up test cases for definitions
to follow.
-/

/-
We define a few variables to use
in the rest of this assignment.
-/
def P : pExp:= varExp (mkVar 0)
def Q: pExp := varExp (mkVar 1)
def R : pExp := varExp (mkVar 2)

/-
We set parameter values used in
some function definitions to follow.
-/
def max_var_index := 2
def num_vars := max_var_index + 1

/-
An example of a propositional logic
expression.
-/
def theExpr : pExp := (P ⇒ (P ∧ R))


/-
An example using the truth_table_results
function to compute and return a list of 
the truth values of theExpr under each of 
its possible interpretations.
-/
#eval truth_table_results theExpr num_vars


/-
#2. Define interp5 to be the interpretation
in the six row (m=5) of the truth table that
our interps_for_n_vars functions returns for
our three variables (P, Q, and R). 

Hint: use the mth_interp_n_vars function.
Definitely check out the definition of the
function, and any specification text, even 
if informal, given with the formal definition.
-/

def interp5 := mth_interp_n_vars 5 3

/-
#3. What Boolean values are assigned to 
P, Q, and R by this interpretation (interp5)? 
Use three #eval commands to compute answers by 
evaluating each variable expressions under the
interp5 interpretation.
-/

#eval pEval P interp5
#eval pEval Q interp5
#eval pEval R interp5

#eval pEval R (mth_interp_n_vars 7 3)
/-
#4. Write a truth table within this
comment block showing the values for
P, Q, and R, in each row in the truth
table, represented by a corresponding
valule in the list of interpretations
returned by interps_for_n_vars. Label
your columns as R, Q, and P, in that
order. (Try to understand why.) 
Hint: Don't just write what you think
the answers are:, evaluate each of
the three variable expression under
each interpretation. You can use the
mth_interp_n_vars function if you want
to obtain interpretation functions for
each of the rows individually if you
want. 

Answer:
   R     Q       P
   -     -       -
   f     f       f
   f     f       t
   f     t       f
   f     t       t
   t     f       f
   t     f       t
   t     t       f
   t     t       t

-/


/-
#5. Write an expression here to
compute the "results" column of
the truth table for "theExpr" as
defined above.
-/

#eval truth_table_results theExpr 2

/-
#6. Copy and paste the truth table
from question #4 here and extend it
with the results you just obtained.
Check the results for correctness.

Answer here:
R     Q       P     Out 
-     -       -     -
f     f       f     t
f     f       t     t
f     t       f     t
f     t       t     t
t     f       f     f
t     f       t     t
t     t       f     f
t     t       t     t

-/

/-
#7.

Write a "predicate" function, isModel,
that takes a propositional logic 
expression, e, and an interpretation, 
i, as its arguments and that returns 
the Boolean true (tt) value if and only
if i is a model of e (otherwise false).
-/

def isModel :pExp → (var → bool) → bool 
| e i := if(pEval e i)
            then tt 
        else ff


#eval  mth_interp_n_vars 3 2( mkVar 0)
#eval isModel P (mth_interp_n_vars 3 2)
/-
#7. Write a one-line implementation
of a function, is_valid, that takes as
its arguments a propositional expression, 
e, and the number of variables, n, in its
truth table, and that returns true if and
only if it is valid, construed to mean
tha every result in the list returned by 
the truth_table_results function is true.

To do so, define and use a fold function
to reduce returned lists of Boolean truth
values to single truth values. Define and
use a bool-specific function, fold_bool :
    (bool → bool → bool) → 
    bool → 
    (list bool) → 
    bool,
where the arguments are, respectively, 
a binary operator, an identity element
for that operator, and a list of bools
to be reduced to a single bool result. 
-/
open list
def fold_bool :
    (bool → bool → bool) → bool → (list bool) → bool
| i val nil := val
| i val (cons h t) := 
    i h (fold_bool i val t)
    


def is_valid : pExp → ℕ → bool
| p n := fold_bool band tt (truth_table_results p n)


/-
Write similar one-line implementations of the
functions, is_satisfiable and is_unsatisfiable, 
respectively. Do not use fold (directly) in your 
implementation of is_unsatisfiable.
-/

def is_satisfiable : pExp → ℕ → bool
| p n := fold_bool bor ff (truth_table_results p n)

def is_unsatisfiable : pExp → ℕ → bool
| p n := if (is_satisfiable p n) then ff else tt

/-
8. Use your is_valid function to determine which
of the following putative valid laws of reasoning
really are valid, and which ones are not. For each
one that is not, give a real-world scenario that
shows that the rule doesn't always lead to a valid
deduction. Use #eval to evaluate the validity of 
each proposition. Use -- to put a comment after
each of the following definitions indicating
either "-- valid" or "-- NOT valid".
-/

def true_intro : pExp := pFalse -- Valid
def false_elim := pFalse ⇒ P -- valid
def and_intro := P ⇒ Q ⇒ (P ∧ Q)   --valid
def and_elim_left := (P ∧ Q) ⇒ P   --valid
def and_elim_right := (P ∧ Q) ⇒ Q  --valid
def or_intro_left := P ⇒ (P ∨ Q) --valid
def or_intro_right := Q ⇒ (P ∨ Q) -- valid
def or_elim := (P ∨ Q) ⇒ (P ⇒ R) ⇒ (Q ⇒ R) ⇒ R -- valid
def iff_intro := (P ⇒ Q) ⇒ (Q ⇒ P) ⇒ (P ↔ Q) -- valid
def iff_elim_left := (P ↔ Q) ⇒ (P ⇒ Q) -- valid
def iff_elim_right := (P ↔ Q) ⇒ (Q ⇒ P) -- valid
def arrow_elim := (P ⇒ Q) ⇒ P ⇒ Q -- valid
def affirm_consequence := (P ⇒ Q) ⇒ Q ⇒ P  --not valid Q=ff P=tt
-- if it is raining then it is wet. Then, if it is wet then it is raining
def resolution := (P ∨ Q) ⇒ (¬ Q ∨ R) ⇒ (P ∨ R) -- valid
def unit_resolution := (P ∨ Q) ⇒ (¬ Q) ⇒ P -- valid
def syllogism := (P ⇒ Q) ⇒ (Q ⇒ R) ⇒ (P ⇒ R) -- valid
def modus_tollens := (P ⇒ Q) ⇒ ¬ Q ⇒ ¬ P -- valid
def neg_elim := ¬ ¬ P ⇒ P -- valid
def excluded_middle := P ∨ ¬ P -- valid
def neg_intro := (P ⇒ pFalse) ⇒ ¬ P -- valid
def affirm_disjunct := (P ∨ Q) ⇒ P ⇒ ¬ Q --Not Valid Q==ff P==ff
-- if it is raining and it is wet, then if it is raining then it is not wet.
def deny_antecedent := (P ⇒ Q) ⇒ (¬ P ⇒ ¬ Q) --Not Valid Q==ff P==ff
-- if it is raining then it is wet. Therefore, if it is not raining it implies it is not wet

-- Answer below
#eval is_valid true_intro 1
#eval is_valid false_elim 1
#eval is_valid and_elim_left 2
#eval is_valid and_elim_right 2
#eval is_valid and_intro 2
#eval is_valid or_intro_left 2
#eval is_valid or_intro_right 2
#eval is_valid or_elim 3
#eval is_valid iff_intro 2
#eval is_valid iff_elim_left 2
#eval is_valid iff_elim_right 2
#eval is_valid arrow_elim 2
#eval is_valid affirm_consequence 2
#eval is_valid resolution 3
#eval is_valid unit_resolution 2
#eval is_valid syllogism 3
#eval is_valid modus_tollens 2
#eval is_valid neg_elim 1
#eval is_valid excluded_middle 1
#eval is_valid neg_intro 1
#eval is_valid affirm_disjunct 2
#eval is_valid deny_antecedent 2