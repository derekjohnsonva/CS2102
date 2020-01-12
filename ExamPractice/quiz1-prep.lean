/-

In lean we represent: (1) propositions as

types and (2) predicates as parameterized

propositions.

 

A parameterized type gives rise to a whole

family of proposition, once for each value

of each parameter.

 

We can think of one-parameter predicates 

as specifying *properties* of objects. As

an example, as defined, is_even : ℕ → Prop

expresses the property of a natural number

(an argument value) "being even". We define

the constructors to ensure that there is a

proof of (is_even n) if and only if (n : ℕ)

is (a term that represents) an even number.

 

One-parameter predicates thus also specify 

*sets* of objects: namely all and only those

values of a given argument type that have the 

specified property as shown by the existence

of a proof that such a value "satisfies the 

predicate" (makes the resulting proposition

true).

 

The is_even predicate thus specifies the

set of all even natural numbers, which we

can write as {0, 2, 4, 6, ...} or, better,

as { n : ℕ | is_even n }.

 

We can think of two-parameter predicates as 

specifying binary relations, that is, sets of

*pairs* of argument values that make a given

proposition true.

 

The most commonplace example of a two-argument

predicate is equals. We can write (_ = _) to 

make it clear that equals takes two values and

yields a proposition that the first equals the

second. For example, if a and b are of type ℕ, 

then (a = b) is a proposition that has a proof

if and only if the two terms really are equal

(when reduced). So, for example, 4 = 2 + 2 is

true, there is a proof of it, because reducing

2 + 2 to 4 reduces the whole proposition to 

4 = 4, and there is a proof of this proposition.

 

The proposition, a = b, in Lean is just a nice

shorthand notation for (eq a b). The two-place

predicate, eq, implements the equality relation. 

It's polymorphic: it takes a *type parameter*, α,

implicitly. It then explicitly takes two values,

a and b, of type α, and yields the proposition, 

a = b (which is of course itself a type).

 

The eq "type builder" (taking α and two values,

a and b of type α) and yielding the proposition

(a type), a = b, provides a single constructor

with which to build proofs. It's called refl,

and it establishes the "reflexive" property of

the eq relation, by taking *any* value, a : α,

for any type, α, and by returning a proof of

(eq a a), that is, of a = a. So, by applying

eq.refl to any value, a, of any type, we get

a proof of (a = a), and those are the *only*

proofs of equality that can be constructed.

There's thus no way to prove that 0 = 1, for

example, because those terms don't reduce to

the same values, and we can only use eq.refl

to construct proofs that two terms are equal

if they really do reduce to exactly the same

value.

 

Finally, we will represent some, but no all,

of the logical connetives, including "and",

"or", and "iff", as polymorphic propositions.

Whereas a predicate, such as eq, will take

values of arbitrary types as arguments (e.g.,

eq can take values of type ℕ), connectives

are like polymorphic types: they take types

as arguments, but in this case the types are

of type Prop.

 

Consider "and" for example. If P and Q are

any two pre-existing propositions (types of

type Prop), then we can form the proposition,

P ∧ Q, and it, too, will be a proposition (a

type of type, Prop). The type of "and" is thus

Prop → Prop → Prop: it takes two propositions

(types of type Prop) as arguments and yields

a new proposition (a new type of type Prop).

 

To enforce the logical meaning of "and", we

define the "and" type builder to have just

one constructor, which we call "intro", that

if applied to a proof, p, of P and to a proof,

q, of Q yields a term, (and.intro p q), that

is axiomatically accepted as being a "proof"

of (and P Q), which we write using an infix

notation as (P ∧ Q). 

 

Finally, we note that if we're given a term,

(and.intro p q), of type (P ∧ Q), that is, if

we're given a proof of (P ∧ Q), we can get a

proof of P from it, by "destructuring" the

term using pattern matching. For example, we

can obtain "p" (the proof of P "contained 

inside" the proof of P ∧ Q) with the following

rule: | (and.intro p _) := p. This is how we

implement the two "elimination rules" for and.

-/

 

/-

Here's a statement of the proposition that

2 + 2 = 4 and a proof of it. 

-/

 

lemma proof_of_two_plus_two_eq_four : 2 + 2 = 4 :=

    eq.refl 4

 

/-

1. State and prove the proposition that the

string,"Lean!", appended to the string, "Hello, "

is equal to the string, "Hello, Lean!". You may

and should use the Lean library-provided string 

append operator, ++, as an infix notation for 

append.

-/

 

-- string append example

#eval "Hi " ++ "There!"

 

-- fill in the blanks

lemma proof1 : "Hi There!" = ("Hi"++"There!"):=
    _

 

/-

2.  Sometimes we want to state and prove a 

proposition without binding a name to the proof.

For that, instead of using def, theorem, or

lemma, we can use "example." Here's an example. 

-/



example : 1 = 1 := eq.refl 1    -- Fill blank with proof.

 

/-

Note that we can use example for ordinary types

as well.

-/

 

example : ℕ := 5

 

/-

2. State and prove the proposition that 3 * 4 = 12,

using "example."

-/

 

-- Answer Here
example : 3 * 4 = 12 :=
begin
    exact eq.refl 12
end
 

/-

3. Use example to formally state and prove the

proposition that 1 = 1 ∧ 0 = 0. 

-/

 

-- Here
example : 1 = 1 ∧ 0 = 0 :=
    and.intro (eq.refl 1) (eq.refl 0)
/-

4. Complete the following program to show that

if P and Q are arbitrary propositions, and *if* 

you're given a proof of P and Q, then you can 

obtain and return a proof of P.

 

Hint: In Lean, and.intro is the one introduction

(proof creating) rule for and, and and.elim_left

and and.elim_right are the two elimination rules.

They are functions. Use one of them!

-/

 

theorem P_and_Q_imp_P {P Q : Prop} (pq : P ∧ Q) : P :=
    and.elim_left pq