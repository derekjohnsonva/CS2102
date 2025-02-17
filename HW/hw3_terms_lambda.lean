-- You can ignore this line for now, but don't remove it.
namespace hw3

/-
In this assignment, you will put into practice your new
knowledge of terms and definitions in predicate logic by
using it to implement a library of Boolean functions. You
will also gain practice using different forms of syntax
for defining functions.
-/

/-
To begin, we present one "unary" Boolean function (taking
one Boolean argument and returning a Boolean result) and one
"binary" function (taking two arguments), using each of three
styles of syntax.
-/

/-
First, here are three implementations of exactly the
same unary function, namely negation, in three styles. 
-/

-- explicitly lambda expression
def neg_bool : bool → bool :=
    λ (b : bool), 
        match b with 
        | ff := tt
        | tt := ff
        end

-- by cases; note absence of := after function type
def neg_bool' : bool → bool
    | ff := tt
    | tt := ff   

-- C-style; note return type is now between : and :=
def neg_bool'' (b : bool) : bool :=
   match b with 
    | ff := tt
    | tt := ff
    end

/-
Second, here are three implementations of exactly the
same binary function (Boolean "and"), in the same three
styles. 
-/

-- Note commas in match expression and in each case
def and_bool : bool → bool → bool :=
    λ (b1 b2 : bool),       --shorthand for two lambdas
        match b1, b2 with   -- matching on two arguments
            | ff, ff := ff
            | ff, tt := ff
            | tt, ff := ff
            | tt, tt := tt
        end

-- Note absence of := and of commas in each of the cases
def and_bool' : bool → bool → bool 
    | ff ff := ff
    | ff tt := ff
    | tt ff := ff
    | tt tt := tt

-- should seem straightforward now
def and_bool'' (b1 b2 : bool) : bool :=
       match b1, b2 with
            | ff, ff := ff
            | ff, tt := ff
            | tt, ff := ff
            | tt, tt := tt
        end

/-
Your homework is to implement the remaining unary Boolean
functions, and several key binary Boolean functions, each
one in each of these styles: lambda, by-cases, and C-style.
-/

/-
1. Implement the always false unary Boolean function in each
of the three styles, lambda, by-cases, and C-style. Call the
functions false_bool, false_bool', and false_bool'', in that
order.
-/

-- Here's the first one, just to get you going.
def false_bool : bool → bool :=
    λ (b : bool),
        ff

-- Now false_bool'
def false_bool' : bool → bool
    | tt := ff
    | ff := ff

-- And now false_bool''
def false_bool'' (b : bool) : bool :=
    ff
/-
2. Do the same for the always true unary Boolean function,
using true_bool as the function name (with zero, one, and 
two ' marks to avoid name conflicts. You will use ' in this
way for each of the remaining parts of this assignment).
-/
def true_bool : bool → bool :=
    λ (b : bool),
        tt

def true_bool' : bool → bool  
    | tt := tt 
    | ff := tt 

def true_bool'' (b : bool) : bool := 
    tt
    

/-
3. Do the same for the unary Boolean identity function,
using ident_bool (and ' variants) as the function name.
-/
def ident_bool : bool → bool :=
    λ (b : bool),
        b

def ident_bool' : bool → bool
    | tt := tt
    | ff := ff

def ident_bool'' (b : bool) : bool :=
    b 

#eval ident_bool'' (ident_bool' (ident_bool (tt)))

/-
Congrats, you now have a small library of all unary Boolean
functions. Now turn to the binary functions. Each will take
two Boolean arguments, we can call them b1 and b2, and will
return a Boolean result.
-/


/-
4. The Boolean "or" function is true if and onlyl if at least 
one of b1 and b2 is true. Equivalently is is false if and only 
if both b1 and b2 are false. Implement this function in each
of the three styles, using or_bool as the function name. You 
may use the example of "and_bool" above as a model. While you
could just cut and paste, we strongly recommend that you type
in your answer, and remaining answers, in full. Learning new
syntax is basically an exercise is "muscle memory". So don't 
take shortcuts here. Learn the syntax now and it will save you
a great deal of frustration later.
-/

def or_bool : bool → bool → bool := 
    λ (b1 b2 : bool),
        match b1, b2 with
            | ff, ff := ff
            | ff, tt := tt
            | tt, tt := tt
            | tt, ff := tt 
        end

def or_bool' : bool → bool → bool 
    | ff ff := ff
    | ff tt := tt
    | tt tt := tt
    | tt ff := tt 

def or_bool'' (b1 b2 : bool) : bool :=
    match b1, b2 with
        | ff, ff := ff
        | ff, tt := tt
        | tt, tt := tt
        | tt, ff := tt 
    end

#eval or_bool tt ff
#eval or_bool' tt ff
#eval or_bool'' tt ff


/-
5. The Boolean "exclusive or" function is true if and only if 
exactly one of its arguments is true. Implement this function
in each style using xor_bool as the function name.
-/

def xor_bool : bool → bool → bool :=
    λ (b1 b2 : bool),
        match b1, b2 with
            | ff, ff := ff
            | ff, tt := tt
            | tt, tt := ff
            | tt, ff := tt 
        end

def xor_bool' : bool → bool → bool 
    | ff ff := ff
    | ff tt := tt
    | tt tt := ff
    | tt ff := tt 

def xor_bool'' (b1 b2 : bool) : bool :=
    match b1, b2 with
        | ff, ff := ff
        | ff, tt := tt
        | tt, tt := ff
        | tt, ff := tt
    end

/-
6. The Boolean "implies" function is true if and only if 
either its first argument is false, or its first argument is 
true and its second argument is also true. Equivalently it is 
false if and only if its first argument is true and its second is false. Implement it in each style, calling it implies_bool.
-/

def implies_bool : bool → bool → bool :=
    λ (b1 b2 : bool),
        match b1, b2 with
            | ff, ff := tt
            | ff, tt := tt
            | tt, tt := tt
            | tt, ff := ff 
        end

def implies_bool' : bool → bool → bool 
    | ff ff := tt
    | ff tt := tt
    | tt tt := tt
    | tt ff := ff 

def implies_bool'' (b1 b2 : bool) : bool :=
    match b1, b2 with
        | ff, ff := tt
        | ff, tt := tt
        | tt, tt := tt
        | tt, ff := ff
    end

/-
7. The Boolean "equivalent" function is true if its two arguments are the same, either both true or both false, 
otherwise it is false. Implement it in the three styles,
using equiv_bool as a function name.
-/
def equiv_bool : bool → bool → bool :=
    λ (b1 b2 : bool),
        match b1, b2 with
            | ff, ff := tt
            | ff, tt := ff
            | tt, tt := tt
            | tt, ff := ff
        end

def equiv_bool' : bool → bool → bool 
    | ff ff := tt
    | ff tt := ff
    | tt tt := tt
    | tt ff := ff 

def equiv_bool'' (b1 b2 : bool) : bool :=
    match b1, b2 with
        | ff, ff := tt
        | ff, tt := ff  
        | tt, tt := tt
        | tt, ff := ff 
    end

-- leave the following in place as the last line in this file
end hw3
