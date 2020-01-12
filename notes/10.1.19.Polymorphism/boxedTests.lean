import .boxed
open boxed_adt

def b1 : boxed nat := boxed.box 3
def b2 : boxed string := boxed.box "Hello"
def b3 : boxed bool := boxed.box tt

def b1' := boxed.box 3 --lean is using type inference

#reduce unbox b1
#reduce unbox b3

