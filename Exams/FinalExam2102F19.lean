/-
Complete exam below. Attest to agreement to honor
code. Submit your exam when done. 
-/

namespace hidden        -- you can ignore this

/-
1. [10 points]

We define a polymorphic tree type. A tree of 
values of type α  is either empty or it is a node 
formed from value of type α along  with two smaller
trees, left and right, of the same kind. The left
and right trees are often called the children of 
a given node. 

We formalize this definition as a polymorphic 
inductive type with two constructors, one, empty, 
with no arguments, and one, with three arguments, 
as follows.
-/

inductive tree (α : Type) : Type
| empty : tree  
| node (value : α) (left : tree) (right : tree) : tree 


/-
1A.  Define three values of type "tree nat": the first,
t1, as the empty tree (of nat); the second, as a tree of nat with
one node, containing the value 5 and with two empty children; and
t3, a tree with 1 value in its "top" node, where each child tree is 
a node with the value 5 and two empty children.

Note: You need to give a type argment explicitly when you use the
empty constructor, but now when you use the node constructor, as
its value can be inferred in the second case.
-/
open tree
--ANSWER
def t1 : tree nat := tree.empty ℕ
def t2 : tree nat := tree.node 5 t1 t1
def t3 : tree nat := tree.node 1 t2 t2

/-
1b. 
Define a function, tree_sum, that takes a value of type 
tree nat, and that returns the *sum* of all of the values
in the given tree. Hint: You may want to test your function
using some of the trees you just defined as arguments.
-/

-- ANSWER 
def tree_sum : (tree nat) → ℕ
| (tree.empty α) := 0
| (tree.node a l r) := a + (tree_sum l) + (tree_sum r)

#eval tree_sum t3
/- 2. [10 points]

The memory of a computer is an array of memory cells
called words. Each word has a numerical "address", from 
zero to the number of words in the memory minus one. If
an address is a represented as a 16-bit value, how big
can the memory of the computer be? 
-/

-- ANSWER
-- 2^16
/-
3. [10 points] 

Define a polymorphic function, tree_to_list,
that takes a value of type tree α as an argument and returns 
a value of type list α, where the returned list contains
all and only the values that appear in the tree: none if
the tree is empty, otherwise the value in the top (given)
node, then all the values in the left child, then all of
the values in the right child. 

Hints: Remember to specify α as the type argument to
tree.empty explicitly, and put parentheses around the
"patterns" to the left of := when pattern matching.
Also, the list namespace is not open by default, so
use list.cons and list.nil for the list constructors.
Remember that list.append can be used to append two
lists. Finally, you might want to test your definition
using the tree values you defined above.
-/
open list
-- ANSWER
def tree_to_list {α : Type} : (tree α) → list α
| (tree.empty α) := list.nil 
| (tree.node a l r) := list.cons a (tree_to_list l) 
/- 4. [15 points]

The next two problems ask you to specify the set of
natural numbers that are multiples of three in two
different ways: first as a simple predicate, and then
as an inductive definition.

4a. Specify a simple predicate (hint, use the mod
function, denoted %) that is true for each multiple
of three and false otherwise.
-/

def mult_three (n: ℕ) : Prop := 
    ∀(n), n%3=0

/-
4b. Specify the set of multiples of three as an
inductively defined family of propositions called 
is_mult_three taking a natural number argument.
The proof constructors should provide proofs for
argument values that are multiples of three and
not for values that are not multiples of three.
Hint: zero is a multiple of three, and, for any
n, if n is a multiple of three, then so is n+3.
-/

inductive is_mult_three : ℕ → Prop
| pf_zero : (is_mult_three 0)
| pf_mult_three : ∀(n : ℕ), is_mult_three (n) → is_mult_three(nat.succ(nat.succ(nat.succ n)))

/- 4c. State and prove the proposition that
9 is a multiple of three: is_mult_three 9.
(Don't use the "mod" version here.)
-/

example : is_mult_three 9 :=
    begin
        apply is_mult_three.pf_mult_three,
        apply is_mult_three.pf_mult_three,
        apply is_mult_three.pf_mult_three,
        apply is_mult_three.pf_zero,        
    end
/- 5. [5 points].

Consider a binary relation, R, on a set 
of values of some arbitrary type, α. In plain
but precise mathematical English, explain what 
it means for R to be transitive. 
-/

-- Answer


/-
6. [10 points] Here we set up a set of assumptions 
and you are to prove a conclusion.
-/

axioms (Raining Sprinkler Wet : Prop)
axiom rw : Raining → Wet
axiom sw : Sprinkler → Wet
axiom h : Raining ∨ Sprinkler

/-
Given these assumptions, prove "Wet". Hint:
it's a one-line proof, very short.
-/
example : Wet :=
    begin
        cases h,
        apply rw h,
        apply sw h,
    end

/- [10 points]
7. Use an inductive definition to formally specify
a ternary (three-place) relation, times_rel,  on ℕ
numbers, such that a triple, (m, n, k) is in the 
relation if  and only if k = m * n, then state and
prove the proposition that the triple, (5, 6, 30),
is in the relation. Hint: You need one constructor.
Call it intro.
-/

-- Answer here
inductive times_rel : nat → nat → nat → Prop
| intro : ∀(m n k : ℕ), (k = m*n) → times_rel m n k

example : times_rel 5 6 30 :=
    begin
        apply times_rel.intro,
        apply eq.refl (30),
    end

/- 8. [10 points] 

Suppose there are balls; that a ball can be made 
of uranium; that a ball can be heavy; and that if
a ball is made from uranium then it is heavy. Prove 
that there if there is a ball made of uranium then
there is a ball that is heavy.
-/

-- Here are the assumptions
axiom Ball : Type
axiom Uranium : Ball → Prop
axiom Heavy : Ball → Prop
axiom uh: ∀ (b : Ball), Uranium b → Heavy b

/-
8a. *Informally* (in English) prove the conjecture
that if there is a Ball that is made of uranium then 
there is a heavy ball. Identify exactly the rules of
inference (introduction and elimination) that you are
using to reach your conclusion. I.e., give a precise
and complete mathematical proof, without constructing
a formal proof.
-/

-- Answer
/-
    Assume that a ball, a, is made of Uranium. Assume the proposition, uh, that
    if a ball is made of Uranium it is also heavy. These two assume statements 
    were reached using introduction. Since it is true that ball a
    is made of urianium, by proposition uh we know that ball a is heavy. This can
    be proven using the definition of implication.
-/


/-
8b. Formally prove the conjecture that if
there is a ball made of uranium, then there is a
heavy ball. Hint: Put parentheses around the major
elements of the proposition to be proved. Second
hint: Lean won't show the preceding axioms as
being in your proof contet, but you may (and
will have to) use at least one of them.
-/

example : (∃ (b : Ball), Uranium b) → ∃ (b : Ball), Heavy b :=
    begin
        intros,
        cases a with b ub,
        have hb := uh b,
        have haevy := hb ub,
        apply exists.intro b,
        assumption,
    end

/- 9. [10 points]

Recall that a binary relation, R, on a set of 
values of some type, α, is said to be asymmetric
if whenever a pair (x, y) is in R, the pair (y, x)
is not; and that R is said to be irreflexive if
for all x, (x, x) is not in R. Give a mathematically
precise but informal (English language) proof that 
if a given binary relation, R, is asymmetric then
it is irreflexive. As part of your proof, define,
using precise but informal mathematical English, 
what each of these properties means. And define
using mathematical notation the conjecture you
are to prove. Identify each inference rule you
use in writing your informal proof.
-/

-- Answer
/-
A binary relation is Asymmetric when the ordering of the 
supplied pair affects the outcome of the relation. For example, 
if R is asymmetric then whenever a pair (x, y) is in R, the pair (y, x)
is not. In mathematical notation, ∀ (x y : α), R x y → ¬ R y x
A binary relation is Irreflexive if applying the same value as both
arguments to the relation result in a statment that is not true. For 
example, a binary relation, R, is irreflexive if the pair (x,x) is not 
in R. In mathematical notation, ∀ (x : α), ¬ R x x

If a binary relation is asymmetric it implies that it is also 
irreflexive. This is shown with the mathematical expression below
     ∀ (α : Type) (F : α → α → Prop), asymmetric F → irreflexive F
Using the mathematical notation for asymmetric and irreflexive from above 
we can write the second half of the Proposition as follows,
    ∀ (x y : α),(R : Bin_op), (R x y → ¬ R y x) → (∀ (x : α),(¬ R x x))
To prove this relation we do the followig
1) Assume there is some value x of type α
2) Assume there is a value rxx that is bin_op R applied to the pair (x,x).
3) Apply value x to the asymmetric definition and call this val rxxnrxx.
    rxxnrxx evaluates to R x x → ¬R x x
4) apply value rxx to the Proposition rxxnrxx. This will yield a value of ¬ R x x
    which we will can nrxx
5) At this point we have a contradiction in our assumptions. A contradiction
    is when two oposite claims are held at the same time. The opposite
    claims that we are holding are rxx and nrxx. Since these can not both 
    be true we have proved irreflexive by contradiction.
        

-/

/-
10. [5 points].

Formally prove the proposition, ¬ false.
-/

example : ¬ false :=
    begin
        apply false.elim, 
    end
/-
11. [5 points] Formally prove the proposition, 
¬ true → false.
-/

-- Answer
example : ¬ true → false :=
    begin
        assume nt,
        apply not.intro nt,
        apply true.intro,
    end

/- Extra credit.
Suppose P and Q are arbitrary propositions. Formally 
prove that,  ¬ ( P ∧ Q) ↔ (¬ P ∨ ¬ Q). Hint: Do you
have to reason classically? Or does it help?
-/

-- Answer

example (P Q : Prop): ¬ ( P ∧ Q) ↔ (¬ P ∨ ¬ Q) :=
    begin
        intros,
        apply iff.intro,
        intros npandq,
        apply or.inl,
        assume p,
         
    end

end hidden      -- You can ignore this