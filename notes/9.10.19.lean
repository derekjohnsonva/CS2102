/-
Natural Language: The language that we all speak.
Not the language that machines operate using. There is too much 
ambiguity in natural language. It is not checkable by machines.

Formal Language: ex Python, boolean algebra. Well defined
language with no ambiguity. Some formal languages are based
off of the structure of natural language(ex. cobol)
-/

/-
General Information for Lean
-/
#check 1 /-the check command checks the type of the thing that follows-/
#eval 1 /-evaluates the following. A literal will just evaluate to itself-/

#eval tt /- tt == true, ff == false-/
#eval ff
#check tt

def n := 1 /-This is known as an identifier-/
/-lean is a functional language so saving a new value to n
is not possible. No mutable state-/
-- def n :=2 
#eval 1 --outputs 1

def n1 : ℕ := (1 : ℕ)  -- natural number symbol is made using \nat 
def b1 : bool := (tt : bool) --this is the syntax we use when we want lean to 
                             --check out types
#check λ (b : bool), tt /-b is an input of type bool that always returns true-/
#reduce λ (b : bool), tt /- λ states that what follows is a function-/

#check λ (b : bool), ff

#check λ (b : bool), b /-a function that outputs whatever is input as long as
it is of type bool-/

#check (λ (b : bool), ff) (tt)    /-This is called an application term-/
/-An application term has two parts. The first is the function expression(λ (b : bool), ff).
The second is the argument expression(tt)-/

def f : bool → bool := λ (b : bool), ff
#eval f ff
#eval f tt

def neg : bool → bool :=
    λ (b : bool), 
        match b with 
        | ff := tt 
        | tt := ff
        end

/-Predicate Logic
    Syntax vs Semantics
        Syntax = grammatical structure
        Semantics = The meanings of symbol arrangement

    Terms in Lean
        Literal: 
        Identifier ("variable"):
        Lambda("function"):
        Application(fn applie to arguments):
-/

-- Function types

#check bool → bool          --unary
#check bool → bool → bool   --binary
#check nat → nat            --unary
#check ℕ  → ℕ → ℕ 
#check ℕ → (ℕ → ℕ)  -- arrow rt assoc

-- Function Values: lambda abstractions

-- take any bool, b; always return ff
def always_false : bool → bool := 
    λ b : bool, tt

-- take any bool, b; always return b
def ident_bool : bool → bool := 
    λ b : bool, b


def weed : (bool → bool) → (ℕ → bool) :=
    λ (a : bool → bool),
        λ( n : ℕ), ff

#check (weed always_false) 5
#eval (weed always_false) 5

def inc_by : ℕ → (ℕ → nat) :=
    λ n : ℕ ,
        λ m : ℕ, m +n
--this is the same as the inc_by method just in a better form
def inc_by'  (n m: ℕ ) : ℕ :=   
    m + n

#check inc_by
#check inc_by 3
#check (inc_by 3) 4
#eval (inc_by 3) 4

-- take a bool and return its complement
def neg_bool (b: bool) : bool :=
    match b with 
    | ff := tt
    | tt := ff
    end
