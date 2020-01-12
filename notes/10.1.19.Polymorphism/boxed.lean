namespace boxed_adt

inductive boxed (T : Type) : Type    --defining the type boxed
| box : T → boxed 

open boxed
def unbox {T : Type} : boxed T → T --{} tell lean to infer an argument
| (box a) := a

end boxed_adt